#!/usr/bin/env python3

import argparse
import json
import re
from pathlib import Path


def load_meta(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def bitwise_or(buffers: list[bytes]) -> bytes:
    if not buffers:
        return b""
    out = bytearray(buffers[0])
    for buf in buffers[1:]:
        if len(buf) != len(out):
            raise ValueError("incompatible bloom binary lengths")
        for i, b in enumerate(buf):
            out[i] |= b
    return bytes(out)


def discover_graph_dirs(root: Path) -> list[Path]:
    return sorted(p.parent for p in root.glob("*/v1/graph.bloom.pred.json"))


def graph_iri_from_source_info(path: Path) -> str | None:
    if not path.exists():
        return None
    text = path.read_text(encoding="utf-8")
    m = re.search(r"fct:graphIri\s+<([^>]+)>", text)
    if not m:
        return None
    return m.group(1)


def selected_graph_dirs(
    root: Path,
    graph_iri_regex: str | None,
    path_regex: str | None,
    metadata_regex: str | None,
    graph_list: Path | None,
) -> list[Path]:
    path_re = re.compile(path_regex) if path_regex else None
    iri_re = re.compile(graph_iri_regex) if graph_iri_regex else None
    meta_re = re.compile(metadata_regex, re.MULTILINE) if metadata_regex else None
    wanted_graphs: set[str] | None = None
    if graph_list is not None:
        wanted_graphs = {
            line.strip()
            for line in graph_list.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.startswith("#")
        }

    selected: list[Path] = []
    for graph_dir in discover_graph_dirs(root):
        source_info = graph_dir / "source-info.ttl"
        graph_iri = graph_iri_from_source_info(source_info)
        if path_re and not path_re.search(str(graph_dir)):
            continue
        if iri_re and not (graph_iri and iri_re.search(graph_iri)):
            continue
        if wanted_graphs is not None and graph_iri not in wanted_graphs:
            continue
        if meta_re:
            text = source_info.read_text(encoding="utf-8") if source_info.exists() else ""
            if not meta_re.search(text):
                continue
        selected.append(graph_dir)
    return selected


def main() -> int:
    parser = argparse.ArgumentParser(description="Roll up per-graph predicate Bloom sidecars into a subset bundle Bloom.")
    parser.add_argument("root", help="Corpus root containing per-graph bloom sidecars")
    parser.add_argument("--output-dir", required=True, help="Directory to write rolled-up bloom files into")
    parser.add_argument("--graph-iri-regex", help="Keep only graphs whose graph IRI matches this regex")
    parser.add_argument("--path-regex", help="Keep only graph directories whose path matches this regex")
    parser.add_argument("--metadata-regex", help="Keep only graphs whose source-info.ttl text matches this regex")
    parser.add_argument("--graph-list", help="File containing one graph IRI per line to include")
    parser.add_argument("--label", default="subset", help="Label recorded in output metadata")
    args = parser.parse_args()

    root = Path(args.root)
    out_dir = Path(args.output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    graph_dirs = selected_graph_dirs(
        root,
        args.graph_iri_regex,
        args.path_regex,
        args.metadata_regex,
        Path(args.graph_list) if args.graph_list else None,
    )
    if not graph_dirs:
        raise SystemExit("no matching graph blooms found")

    metas = [load_meta(graph_dir / "graph.bloom.pred.json") for graph_dir in graph_dirs]
    first = metas[0]
    bit_count = int(first["bit_count"])
    hash_count = int(first["hash_count"])
    binary_name = str(first["binary"])
    incompatible = [
        graph_dir for graph_dir, meta in zip(graph_dirs, metas)
        if int(meta["bit_count"]) != bit_count
        or int(meta["hash_count"]) != hash_count
        or str(meta["binary"]) != binary_name
    ]
    if incompatible:
        raise SystemExit(
            "matching graph blooms are not OR-compatible; regenerate them with a shared "
            "--fixed-bit-count and hash-count before roll-up"
        )

    buffers = [(graph_dir / binary_name).read_bytes() for graph_dir in graph_dirs]
    rolled = bitwise_or(buffers)
    out_bin = out_dir / "bundle.bloom.pred.bin"
    out_json = out_dir / "bundle.bloom.pred.json"
    out_bin.write_bytes(rolled)
    out_json.write_text(
        json.dumps(
            {
                "kind": "predicate-bloom-bundle-v1",
                "label": args.label,
                "graph_count": len(graph_dirs),
                "bit_count": bit_count,
                "hash_count": hash_count,
                "binary": out_bin.name,
                "selection": {
                    "graph_iri_regex": args.graph_iri_regex,
                    "path_regex": args.path_regex,
                    "metadata_regex": args.metadata_regex,
                    "graph_list": args.graph_list,
                },
                "graphs": [str(graph_iri_from_source_info(graph_dir / "source-info.ttl") or graph_dir) for graph_dir in graph_dirs],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"root={root}")
    print(f"output_dir={out_dir}")
    print(f"graphs={len(graph_dirs)}")
    print(f"bit_count={bit_count}")
    print(f"hash_count={hash_count}")
    print(f"label={args.label}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
