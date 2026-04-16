#!/usr/bin/env python3

import argparse
import os
import sys

from rdflib import ConjunctiveGraph, Graph


FORMAT_BY_EXT = {
    ".ttl": "turtle",
    ".trig": "trig",
    ".nt": "nt",
    ".nq": "nquads",
    ".rdf": "xml",
    ".xml": "xml",
}


def detect_format(path: str) -> str:
    ext = os.path.splitext(path)[1].lower()
    fmt = FORMAT_BY_EXT.get(ext)
    if fmt is None:
        raise ValueError(f"cannot infer RDF format from extension: {path}")
    return fmt


def load_graph(path: str, rdf_format: str):
    if rdf_format in {"trig", "nquads"}:
        graph = ConjunctiveGraph()
    else:
        graph = Graph()
    graph.parse(path, format=rdf_format)
    return graph


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Convert RDF files between common serialization formats using rdflib."
    )
    parser.add_argument("input", help="input RDF file")
    parser.add_argument("output", help="output RDF file")
    parser.add_argument("--input-format", dest="input_format", help="explicit input format")
    parser.add_argument("--output-format", dest="output_format", help="explicit output format")
    args = parser.parse_args()

    input_format = args.input_format or detect_format(args.input)
    output_format = args.output_format or detect_format(args.output)

    graph = load_graph(args.input, input_format)
    graph.serialize(destination=args.output, format=output_format)

    kind = "dataset" if output_format in {"trig", "nquads"} else "graph"
    print(f"input={args.input}")
    print(f"output={args.output}")
    print(f"input_format={input_format}")
    print(f"output_format={output_format}")
    print(f"{kind}_size={len(graph)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
