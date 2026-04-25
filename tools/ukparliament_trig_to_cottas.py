#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import struct
import sys
import time
from dataclasses import dataclass
from pathlib import Path

import duckdb
import pandas as pd
from pyoxigraph import parse
from rdflib import Graph, Literal, Namespace, URIRef
from rdflib.namespace import DCTERMS, RDF, XSD


FCT = Namespace("https://factoidal.example/ns/corpus#")
ID = Namespace("https://factoidal.example/id/")


@dataclass
class ParsedLine:
    subject_text: str
    predicate_text: str
    object_text: str
    graph_text: str


def slugify(text: str) -> str:
    slug = re.sub(r"[^a-zA-Z0-9._-]+", "-", text).strip("-").lower()
    return slug or "dataset"


def ensure_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def write_text(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")


def write_source_info(
    path: Path,
    graph_iri: str,
    source_path: str,
    source_format: str,
    triple_count: int,
    artifact_format: str,
) -> None:
    content = f"""@prefix dct: <http://purl.org/dc/terms/> .
@prefix fct: <https://factoidal.example/ns/corpus#> .

<> a fct:CorpusGraphChunk ;
  fct:graphIri <{graph_iri}> ;
  dct:source "{source_path}" ;
  dct:format "{source_format}" ;
  fct:tripleCount "{triple_count}" ;
  fct:artifactFormat "{artifact_format}" .
"""
    write_text(path, content)


def add_toc_entry(
    g: Graph,
    dataset_name: str,
    graph_iri: str,
    chunk_name: str,
    version: str,
    triple_count: int,
    artifact_relpath: str,
    source_path: str,
    source_format: str,
    artifact_format: str,
) -> None:
    chunk = URIRef(f"{ID}corpus/{dataset_name}/{chunk_name}/{version}")
    graph_ref = URIRef(graph_iri)
    artifact = URIRef(f"{chunk}/artifact")
    g.add((chunk, RDF.type, FCT.CorpusGraphChunk))
    g.add((chunk, DCTERMS.identifier, Literal(chunk_name)))
    g.add((chunk, FCT.graphIri, graph_ref))
    g.add((chunk, FCT.versionLabel, Literal(version)))
    g.add((chunk, FCT.relativePath, Literal(artifact_relpath)))
    g.add((chunk, FCT.tripleCount, Literal(triple_count, datatype=XSD.integer)))
    g.add((chunk, DCTERMS.source, Literal(source_path)))
    g.add((chunk, DCTERMS["format"], Literal(source_format)))
    g.add((chunk, FCT.artifact, artifact))
    g.add((artifact, RDF.type, FCT.CorpusArtifact))
    g.add((artifact, FCT.relativePath, Literal(artifact_relpath)))
    g.add((artifact, DCTERMS["format"], Literal(artifact_format)))


def write_toc(
    toc_path: Path,
    dataset_name: str,
    graph_iri: str,
    chunk_name: str,
    version: str,
    triple_count: int,
    artifact_relpath: str,
    source_path: str,
    source_format: str,
    artifact_format: str,
) -> None:
    toc = Graph()
    toc.bind("dct", DCTERMS)
    toc.bind("fct", FCT)
    add_toc_entry(
        toc,
        dataset_name=dataset_name,
        graph_iri=graph_iri,
        chunk_name=chunk_name,
        version=version,
        triple_count=triple_count,
        artifact_relpath=artifact_relpath,
        source_path=source_path,
        source_format=source_format,
        artifact_format=artifact_format,
    )
    toc.serialize(destination=toc_path, format="nt", encoding="utf-8")


def skip_ws(text: str, pos: int) -> int:
    while pos < len(text) and text[pos] in " \t":
        pos += 1
    return pos


def scan_iri(text: str, pos: int) -> int:
    if pos >= len(text) or text[pos] != "<":
        raise ValueError("expected IRI")
    pos += 1
    while pos < len(text):
        ch = text[pos]
        if ch == ">":
            return pos + 1
        if ch == "\\":
            if pos + 1 >= len(text):
                raise ValueError("unterminated IRI escape")
            esc = text[pos + 1]
            if esc == "u":
                pos += 6
            elif esc == "U":
                pos += 10
            else:
                raise ValueError("invalid IRI escape")
            continue
        pos += 1
    raise ValueError("unterminated IRI")


def scan_bnode(text: str, pos: int) -> int:
    if not text.startswith("_:", pos):
        raise ValueError("expected blank node")
    pos += 2
    start = pos
    while pos < len(text) and text[pos] not in " \t":
        pos += 1
    if pos == start:
        raise ValueError("empty blank node")
    return pos


def scan_literal(text: str, pos: int) -> int:
    if pos >= len(text) or text[pos] != '"':
        raise ValueError("expected literal")
    pos += 1
    while pos < len(text):
        ch = text[pos]
        if ch == "\\":
            if pos + 1 >= len(text):
                raise ValueError("unterminated literal escape")
            esc = text[pos + 1]
            if esc == "u":
                pos += 6
            elif esc == "U":
                pos += 10
            else:
                pos += 2
            continue
        if ch == '"':
            pos += 1
            break
        pos += 1
    else:
        raise ValueError("unterminated literal")

    if pos < len(text) and text[pos] == "@":
        pos += 1
        while pos < len(text) and text[pos] not in " \t":
            pos += 1
        return pos
    if pos + 1 < len(text) and text[pos] == "^" and text[pos + 1] == "^":
        pos += 2
        return scan_iri(text, pos)
    return pos


def scan_term(text: str, pos: int) -> int:
    if pos >= len(text):
        raise ValueError("unexpected end of line")
    if text[pos] == "<":
        return scan_iri(text, pos)
    if text.startswith("_:", pos):
        return scan_bnode(text, pos)
    if text[pos] == '"':
        return scan_literal(text, pos)
    raise ValueError("unsupported term start")


def parse_nq_line(line: str) -> ParsedLine | None:
    stripped = line.strip()
    if not stripped or stripped.startswith("#"):
        return None

    text = line.rstrip("\r\n")
    pos = skip_ws(text, 0)
    subj_start = pos
    s_end = scan_term(text, pos)
    subject_text = text[subj_start:s_end]
    pos = skip_ws(text, s_end)
    pred_start = pos
    p_end = scan_iri(text, pos)
    predicate_text = text[pred_start:p_end]
    pos = skip_ws(text, p_end)
    obj_start = pos
    o_end = scan_term(text, pos)
    object_text = text[obj_start:o_end]
    pos = skip_ws(text, o_end)

    graph_text = "DEFAULT"
    if pos < len(text) and text[pos] != ".":
        graph_start = pos
        graph_end = scan_term(text, pos)
        graph_text = text[graph_start:graph_end]
        pos = skip_ws(text, graph_end)

    if pos >= len(text) or text[pos] != ".":
        raise ValueError("expected terminating dot")

    return ParsedLine(
        subject_text=subject_text,
        predicate_text=predicate_text,
        object_text=object_text,
        graph_text=graph_text,
    )


def write_factbin_from_nq(data_nq_path: Path, factbin_path: Path) -> None:
    terms: list[str] = []
    term_ids: dict[str, int] = {}
    graphs: list[str] = []
    graph_ids: dict[str, int] = {}
    quads: list[tuple[int, int, int, int]] = []

    def intern_term(token: str) -> int:
        existing = term_ids.get(token)
        if existing is not None:
            return existing
        idx = len(terms)
        terms.append(token)
        term_ids[token] = idx
        return idx

    def intern_graph(token: str) -> int:
        existing = graph_ids.get(token)
        if existing is not None:
            return existing
        idx = len(graphs)
        graphs.append(token)
        graph_ids[token] = idx
        return idx

    with data_nq_path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            try:
                parsed = parse_nq_line(line)
            except Exception as exc:
                raise RuntimeError(f"{data_nq_path}:{line_no}: {exc}") from exc
            if parsed is None:
                continue
            quads.append(
                (
                    intern_term(parsed.subject_text),
                    intern_term(parsed.predicate_text),
                    intern_term(parsed.object_text),
                    intern_graph(parsed.graph_text),
                )
            )

    with factbin_path.open("wb") as out:
        out.write(b"FTDBIN1\n")
        out.write(struct.pack("<III", len(terms), len(graphs), len(quads)))
        for token in terms:
            encoded = token.encode("utf-8")
            out.write(struct.pack("<I", len(encoded)))
            out.write(encoded)
        for graph in graphs:
            encoded = graph.encode("utf-8")
            out.write(struct.pack("<I", len(encoded)))
            out.write(encoded)
        for s_id, p_id, o_id, g_id in quads:
            out.write(struct.pack("<IIII", s_id, p_id, o_id, g_id))


def maybe_verify_cottas(cottas_path: Path) -> tuple[bool | None, dict[str, object] | None]:
    try:
        import pycottas
    except ImportError:
        return None, None
    return bool(pycottas.verify(str(cottas_path))), dict(pycottas.info(str(cottas_path)))


def stream_trig_to_nq_and_duckdb(
    input_path: Path,
    data_nq_path: Path,
    con: duckdb.DuckDBPyConnection,
    batch_size: int,
    progress_every: int,
    quad_limit: int | None,
) -> tuple[int, set[str]]:
    quad_count = 0
    named_graphs: set[str] = set()
    batch: list[tuple[str, str, str, str]] = []
    started = time.time()

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
            s = str(quad.subject)
            p = str(quad.predicate)
            o = str(quad.object)
            g = str(quad.graph_name)
            if g == "DEFAULT":
                g = "DEFAULT"
                out.write(f"{s} {p} {o} .\n")
            else:
                named_graphs.add(g)
                out.write(f"{s} {p} {o} {g} .\n")

            batch.append((s, p, o, g))
            quad_count += 1

            if len(batch) >= batch_size:
                flush_batch()

            if progress_every > 0 and quad_count % progress_every == 0:
                elapsed = time.time() - started
                print(
                    f"progress quads={quad_count} named_graphs={len(named_graphs)} elapsed_s={elapsed:.1f}",
                    file=sys.stderr,
                    flush=True,
                )

            if quad_limit is not None and quad_count >= quad_limit:
                break

        flush_batch()

    return quad_count, named_graphs


def write_cottas_parquet(
    con: duckdb.DuckDBPyConnection,
    cottas_path: Path,
    index: str,
) -> None:
    if cottas_path.exists():
        cottas_path.unlink()
    order_cols = ", ".join(index.lower())
    con.execute(
        f"""
        COPY (
          SELECT DISTINCT s, p, o, g
          FROM quads
          ORDER BY {order_cols}
        ) TO ?
        (
          FORMAT PARQUET,
          COMPRESSION ZSTD,
          COMPRESSION_LEVEL 22,
          PARQUET_VERSION v2,
          STRING_DICTIONARY_PAGE_SIZE_LIMIT 1,
          KV_METADATA {{index: ?}}
        )
        """,
        [str(cottas_path), index.lower()],
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Parse the UK Parliament TriG dump with a streaming pyoxigraph iterator "
            "and materialize a Factoidal/F* COTTAS-style corpus directory."
        )
    )
    parser.add_argument(
        "--input",
        default="third_party/data/ukparliament/ukparliament-rdf-2019-07-27.trig",
        help="Input TriG file",
    )
    parser.add_argument(
        "--corpus-root",
        default="tmp/ukparliament/CorpusCOTTAS",
        help="Output corpus root to create",
    )
    parser.add_argument(
        "--dataset-name",
        default="ukparliament",
        help="Logical dataset name used in the output layout",
    )
    parser.add_argument(
        "--chunk-name",
        help="Optional stable chunk directory name; defaults to dataset-name slug",
    )
    parser.add_argument(
        "--dataset-iri",
        help="Synthetic dataset IRI written into source-info and toc metadata",
    )
    parser.add_argument(
        "--version",
        default="v1",
        help="Version directory label",
    )
    parser.add_argument(
        "--index",
        default="spog",
        choices=["spo", "spog", "posg", "ospg"],
        help="Column order metadata for Parquet materialization",
    )
    parser.add_argument(
        "--duckdb-path",
        help="Optional DuckDB scratch database path; defaults inside the chunk directory",
    )
    parser.add_argument(
        "--keep-duckdb",
        action="store_true",
        help="Keep the temporary DuckDB database instead of deleting it",
    )
    parser.add_argument(
        "--batch-size",
        type=int,
        default=200000,
        help="Rows per batch inserted into DuckDB",
    )
    parser.add_argument(
        "--progress-every",
        type=int,
        default=200000,
        help="Emit a progress line to stderr every N quads",
    )
    parser.add_argument(
        "--quad-limit",
        type=int,
        help="Optional limit for smoke-testing on a prefix of the parsed dataset",
    )
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    input_path = Path(args.input).resolve()
    corpus_root = Path(args.corpus_root).resolve()
    chunk_name = args.chunk_name or slugify(args.dataset_name)
    chunk_dir = corpus_root / chunk_name / args.version
    toc_dir = corpus_root / "toc"
    ensure_dir(chunk_dir)
    ensure_dir(toc_dir)

    data_nq_path = chunk_dir / "data.nq"
    factbin_path = chunk_dir / "data.factbin"
    cottas_path = chunk_dir / "data.cottas"
    summary_path = chunk_dir / "summary.json"
    source_info_path = chunk_dir / "source-info.ttl"
    toc_path = toc_dir / "data.nt"
    duckdb_path = Path(args.duckdb_path).resolve() if args.duckdb_path else chunk_dir / "materialize.duckdb"
    dataset_iri = args.dataset_iri or f"urn:factoidal:dataset:{slugify(args.dataset_name)}"

    if duckdb_path.exists():
        duckdb_path.unlink()

    started = time.time()
    con = duckdb.connect(str(duckdb_path))
    try:
        con.execute("SET preserve_insertion_order = false")
        con.execute("SET enable_progress_bar = false")
        con.execute(
            """
            CREATE TABLE quads (
              s VARCHAR NOT NULL,
              p VARCHAR NOT NULL,
              o VARCHAR NOT NULL,
              g VARCHAR NOT NULL
            )
            """
        )

        quad_count, named_graphs = stream_trig_to_nq_and_duckdb(
            input_path=input_path,
            data_nq_path=data_nq_path,
            con=con,
            batch_size=args.batch_size,
            progress_every=args.progress_every,
            quad_limit=args.quad_limit,
        )
        write_cottas_parquet(con, cottas_path, args.index)
    finally:
        con.close()

    write_factbin_from_nq(data_nq_path, factbin_path)
    verified, cottas_info = maybe_verify_cottas(cottas_path)

    write_source_info(
        source_info_path,
        graph_iri=dataset_iri,
        source_path=str(input_path),
        source_format="application/trig",
        triple_count=quad_count,
        artifact_format="application/vnd.cottas",
    )
    write_toc(
        toc_path,
        dataset_name=args.dataset_name,
        graph_iri=dataset_iri,
        chunk_name=chunk_name,
        version=args.version,
        triple_count=quad_count,
        artifact_relpath=os.path.relpath(cottas_path, corpus_root),
        source_path=str(input_path),
        source_format="application/trig",
        artifact_format="application/vnd.cottas",
    )

    summary = {
        "artifact_type": "duckdb-cottas",
        "source_path": str(input_path),
        "source_format": "application/trig",
        "dataset_name": args.dataset_name,
        "version": args.version,
        "quad_count": quad_count,
        "graph_count": len(named_graphs),
        "index": args.index.lower(),
        "verified": verified,
        "cottas_info": cottas_info,
        "files": {
            "data_cottas": "data.cottas",
            "data_factbin": "data.factbin",
            "data_nq": "data.nq",
            "source_info": "source-info.ttl",
        },
        "elapsed_s": round(time.time() - started, 3),
        "streaming_parser": "pyoxigraph",
        "batch_size": args.batch_size,
    }
    write_text(summary_path, json.dumps(summary, indent=2) + "\n")

    if not args.keep_duckdb and duckdb_path.exists():
        duckdb_path.unlink()

    print(f"corpus_root={corpus_root}")
    print(f"chunk={chunk_name}")
    print(f"artifact={cottas_path}")
    print(f"quads={quad_count}")
    print(f"graphs={len(named_graphs)}")
    print(f"verified={verified}")
    print(f"elapsed_s={time.time() - started:.3f}")
    print(f"toc={toc_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
