#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

from pyoxigraph import parse as pyoxigraph_parse
from rdflib import Graph, URIRef
from rdflib.parser import create_input_source
from rdflib.plugin import get as rdflib_plugin_get
from rdflib.store import Store


RDFLIB_PARSER_NAME = {
    "trig": "trig",
    "turtle": "turtle",
    "nt": "nt",
    "nq": "nquads",
    "rdfxml": "xml",
}

PYOXIGRAPH_MIME = {
    "trig": "application/trig",
    "turtle": "text/turtle",
    "nt": "application/n-triples",
    "nq": "application/n-quads",
    "rdfxml": "application/rdf+xml",
}


class CountingStore(Store):
    context_aware = True
    formula_aware = False
    graph_aware = True

    def __init__(self, progress_every: int = 0, label: str = "rdflib") -> None:
        super().__init__()
        self.progress_every = progress_every
        self.label = label
        self.started = time.time()
        self.count = 0
        self.named_graphs: set[str] = set()
        self.default_graph_identifiers: set[str] = set()
        self._prefix_to_ns: dict[str, str] = {}
        self._ns_to_prefix: dict[str, str] = {}

    def _note_progress(self) -> None:
        if self.progress_every > 0 and self.count % self.progress_every == 0:
            elapsed = time.time() - self.started
            print(
                f"progress parser={self.label} count={self.count} named_graphs={len(self.named_graphs)} elapsed_s={elapsed:.1f}",
                file=sys.stderr,
                flush=True,
            )

    def open(self, configuration, create=False):  # noqa: ANN001,ANN201
        return self

    def close(self, commit_pending_transaction=False):  # noqa: ANN001,ANN201
        return None

    def destroy(self, configuration):  # noqa: ANN001,ANN201
        return None

    def add(self, triple, context, quoted=False):  # noqa: ANN001,ANN201
        self.count += 1
        if context is not None:
            ident = getattr(context, "identifier", context)
            ident_str = str(ident)
            if ident_str not in ("", "urn:x-rdflib:default") and ident_str not in self.default_graph_identifiers:
                self.named_graphs.add(ident_str)
        self._note_progress()

    def addN(self, quads):  # noqa: ANN001,ANN201,N802
        for s, p, o, c in quads:
            self.add((s, p, o), c)

    def remove(self, triple, context=None):  # noqa: ANN001,ANN201
        return None

    def triples(self, triple_pattern, context=None):  # noqa: ANN001,ANN201
        if False:
            yield triple_pattern, iter(())
        return

    def __len__(self, context=None):  # noqa: ANN001
        return self.count

    def contexts(self, triple=None):  # noqa: ANN001,ANN201
        return iter(())

    def add_graph(self, graph):  # noqa: ANN001,ANN201
        return None

    def remove_graph(self, graph):  # noqa: ANN001,ANN201
        return None

    def bind(self, prefix, namespace, override=True):  # noqa: ANN001,ANN201
        ns = str(namespace)
        self._prefix_to_ns[str(prefix)] = ns
        self._ns_to_prefix[ns] = str(prefix)

    def prefix(self, namespace):  # noqa: ANN001,ANN201
        return self._ns_to_prefix.get(str(namespace))

    def namespace(self, prefix):  # noqa: ANN001,ANN201
        ns = self._prefix_to_ns.get(str(prefix))
        return URIRef(ns) if ns is not None else None

    def namespaces(self):  # noqa: ANN201
        for prefix, ns in self._prefix_to_ns.items():
            yield prefix, URIRef(ns)


def count_with_pyoxigraph(input_path: Path, rdf_format: str, progress_every: int) -> tuple[int, int, float]:
    count = 0
    named_graphs: set[str] = set()
    started = time.time()
    with input_path.open("rb") as handle:
        for quad_or_triple in pyoxigraph_parse(handle, PYOXIGRAPH_MIME[rdf_format]):
            count += 1
            graph_name = getattr(quad_or_triple, "graph_name", None)
            if graph_name is not None and str(graph_name) != "DEFAULT":
                named_graphs.add(str(graph_name))
            if progress_every > 0 and count % progress_every == 0:
                elapsed = time.time() - started
                print(
                    f"progress parser=pyoxigraph count={count} named_graphs={len(named_graphs)} elapsed_s={elapsed:.1f}",
                    file=sys.stderr,
                    flush=True,
                )
    return count, len(named_graphs), time.time() - started


def count_with_rdflib(input_path: Path, rdf_format: str, progress_every: int) -> tuple[int, int, float]:
    started = time.time()
    store = CountingStore(progress_every=progress_every, label="rdflib")
    graph = Graph(store=store)
    store.default_graph_identifiers.add(str(graph.identifier))
    source = create_input_source(location=str(input_path))
    parser_cls = rdflib_plugin_get(RDFLIB_PARSER_NAME[rdf_format], kind=__import__("rdflib.parser").parser.Parser)
    parser = parser_cls()
    parser.parse(source, graph)
    return store.count, len(store.named_graphs), time.time() - started


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Count RDF statements with pyoxigraph and rdflib, without materializing output artifacts."
    )
    parser.add_argument("input", help="RDF input file")
    parser.add_argument(
        "--format",
        choices=sorted(RDFLIB_PARSER_NAME),
        default="trig",
        help="Input RDF format",
    )
    parser.add_argument(
        "--parser",
        choices=["both", "pyoxigraph", "rdflib"],
        default="both",
        help="Which parser(s) to run",
    )
    parser.add_argument(
        "--progress-every",
        type=int,
        default=200000,
        help="Emit progress every N statements",
    )
    return parser


def main() -> int:
    args = build_parser().parse_args()
    input_path = Path(args.input).resolve()

    results: list[tuple[str, int, int, float]] = []
    if args.parser in ("both", "pyoxigraph"):
        count, named_graphs, elapsed = count_with_pyoxigraph(input_path, args.format, args.progress_every)
        results.append(("pyoxigraph", count, named_graphs, elapsed))
    if args.parser in ("both", "rdflib"):
        count, named_graphs, elapsed = count_with_rdflib(input_path, args.format, args.progress_every)
        results.append(("rdflib", count, named_graphs, elapsed))

    for parser_name, count, named_graphs, elapsed in results:
        print(f"parser={parser_name}")
        print(f"count={count}")
        print(f"named_graphs={named_graphs}")
        print(f"elapsed_s={elapsed:.3f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
