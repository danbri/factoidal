#!/usr/bin/env python3

import argparse
from pathlib import Path


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Generate deterministic synthetic N-Quads data")
    parser.add_argument("--output", required=True, help="Output .nq path")
    parser.add_argument("--subjects", type=int, default=1000, help="Number of subjects")
    parser.add_argument("--graphs", type=int, default=4, help="Number of named graphs")
    parser.add_argument("--fanout", type=int, default=3, help="Outgoing links per subject")
    parser.add_argument("--types", type=int, default=16, help="Distinct rdf:type values")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)

    with output.open("w", encoding="utf-8") as handle:
        for idx in range(args.subjects):
            subj = f"<urn:synthetic:s:{idx}>"
            status = "\"active\"" if idx % 2 == 0 else "\"inactive\""
            score = f"\"{idx}\"^^<http://www.w3.org/2001/XMLSchema#integer>"
            handle.write(f"{subj} <urn:synthetic:status> {status} .\n")
            handle.write(f"{subj} <urn:synthetic:score> {score} .\n")
            handle.write(
                f"{subj} <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> "
                f"<urn:synthetic:Type:{idx % args.types}> .\n"
            )

            for graph_idx in range(args.graphs):
                graph = f"<urn:synthetic:g:{graph_idx}>"
                handle.write(f"{subj} <urn:synthetic:name> \"Subject {idx}\" {graph} .\n")
                handle.write(f"{subj} <urn:synthetic:graph> {graph} {graph} .\n")
                for hop in range(args.fanout):
                    target = (idx + graph_idx + hop + 1) % args.subjects
                    handle.write(
                        f"{subj} <urn:synthetic:knows> <urn:synthetic:s:{target}> {graph} .\n"
                    )

    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

