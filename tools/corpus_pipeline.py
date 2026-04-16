#!/usr/bin/env python3

import argparse
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import zlib
from dataclasses import dataclass
from pathlib import Path

from rdflib import Graph, Literal, Namespace, URIRef
from rdflib.namespace import DCTERMS, RDF, XSD


FCT = Namespace("https://factoidal.example/ns/corpus#")
ID = Namespace("https://factoidal.example/id/")


@dataclass
class ParsedLine:
    triple_text: str
    graph_iri: str | None
    subject_text: str
    predicate_text: str
    object_text: str
    graph_text: str | None


@dataclass
class BucketWriter:
    handle: object
    line_count: int
    byte_count: int


def slugify(text: str) -> str:
    slug = re.sub(r"[^a-zA-Z0-9._-]+", "-", text).strip("-").lower()
    return slug or "graph"


def ensure_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


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


def parse_nt_or_nq_line(line: str, input_format: str) -> ParsedLine | None:
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
    triple_text = text[:o_end]
    pos = skip_ws(text, o_end)

    graph_iri = None
    graph_text = None
    if input_format == "nq":
        if pos < len(text) and text[pos] != ".":
            g_start = pos
            g_end = scan_term(text, pos)
            graph_text = text[g_start:g_end]
            if graph_text.startswith("<") and graph_text.endswith(">"):
                graph_iri = graph_text[1:-1]
            elif graph_text.startswith("_:"):
                graph_iri = f"urn:factoidal:bnode-graph:{graph_text[2:]}"
            else:
                raise ValueError("invalid graph term")
            pos = skip_ws(text, g_end)

    if pos >= len(text) or text[pos] != ".":
        raise ValueError("expected terminating dot")

    return ParsedLine(
        triple_text=triple_text + " .",
        graph_iri=graph_iri,
        subject_text=subject_text,
        predicate_text=predicate_text,
        object_text=object_text,
        graph_text=graph_text,
    )


def write_source_info(path: Path, graph_iri: str, source_path: str, source_format: str, triple_count: int, artifact_format: str) -> None:
    content = f"""@prefix dct: <http://purl.org/dc/terms/> .
@prefix fct: <https://factoidal.example/ns/corpus#> .

<> a fct:CorpusGraphChunk ;
  fct:graphIri <{graph_iri}> ;
  dct:source "{source_path}" ;
  dct:format "{source_format}" ;
  fct:tripleCount "{triple_count}" ;
  fct:artifactFormat "{artifact_format}" .
"""
    path.write_text(content, encoding="utf-8")


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


def maybe_build_hdt(hdt_command: str | None, nt_path: Path, hdt_path: Path) -> bool:
    if not hdt_command:
        return False
    tool = shutil.which(hdt_command)
    if not tool:
        return False
    subprocess.run([tool, str(nt_path), str(hdt_path)], check=True)
    return hdt_path.exists()


def bucket_chunk_name(graph_iri: str, bucket_count: int) -> str:
    bucket = zlib.crc32(graph_iri.encode("utf-8")) % bucket_count
    width = max(3, len(str(bucket_count - 1)))
    return f"bucket-{bucket:0{width}d}"


def hash_bucket_name(graph_iri: str, bucket_count: int) -> str:
    digest = hashlib.sha256(graph_iri.encode("utf-8")).digest()
    bucket = int.from_bytes(digest[:8], "big") % bucket_count
    width = max(4, len(str(bucket_count - 1)))
    return f"bucket-{bucket:0{width}d}"


def write_text(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")


def write_factbin(path: Path, rows: list[ParsedLine]) -> None:
    terms: list[str] = []
    term_ids: dict[str, int] = {}
    graphs: list[str] = [""]
    graph_ids: dict[str, int] = {"": 0}
    quads: list[tuple[int, int, int, int]] = []

    def intern_term(token: str) -> int:
        existing = term_ids.get(token)
        if existing is not None:
            return existing
        idx = len(terms)
        terms.append(token)
        term_ids[token] = idx
        return idx

    def intern_graph(token: str | None) -> int:
        key = token or ""
        existing = graph_ids.get(key)
        if existing is not None:
            return existing
        idx = len(graphs)
        graphs.append(key)
        graph_ids[key] = idx
        return idx

    for row in rows:
        quads.append(
            (
                intern_term(row.subject_text),
                intern_term(row.predicate_text),
                intern_term(row.object_text),
                intern_graph(row.graph_text),
            )
        )

    with path.open("wb") as handle:
        handle.write(b"FTDBIN1\n")
        handle.write(struct.pack("<III", len(terms), len(graphs), len(quads)))
        for token in terms:
            encoded = token.encode("utf-8")
            handle.write(struct.pack("<I", len(encoded)))
            handle.write(encoded)
        for graph in graphs:
            encoded = graph.encode("utf-8")
            handle.write(struct.pack("<I", len(encoded)))
            handle.write(encoded)
        for s_id, p_id, o_id, g_id in quads:
            handle.write(struct.pack("<IIII", s_id, p_id, o_id, g_id))


def append_text(path: Path, text: str) -> None:
    with path.open("a", encoding="utf-8") as out:
        out.write(text)


def write_materialize_progress(path: Path, **fields: object) -> None:
    write_text(path, "\n".join(f"{k}={v}" for k, v in fields.items()) + "\n")


def source_info_field(text: str, predicate: str) -> str | None:
    m = re.search(rf"{re.escape(predicate)}\s+\"([^\"]*)\"", text)
    if m:
        return m.group(1)
    return None


def source_info_graph_iri(text: str) -> str | None:
    m = re.search(r"fct:graphIri\s+<([^>]+)>", text)
    if m:
        return m.group(1)
    return None


@dataclass
class MaterializedEntry:
    chunk_name: str
    version: str
    graph_iri: str
    triple_count: int
    artifact_relpath: str
    source_path: str
    source_format: str
    artifact_format: str


def load_materialized_entries(corpus_root: Path, version: str) -> dict[str, MaterializedEntry]:
    entries: dict[str, MaterializedEntry] = {}
    for source_info_path in corpus_root.glob(f"*/{version}/source-info.ttl"):
        chunk_dir = source_info_path.parent
        chunk_name = chunk_dir.parent.name
        text = source_info_path.read_text(encoding="utf-8")
        graph_iri = source_info_graph_iri(text)
        triple_count_text = source_info_field(text, "fct:tripleCount")
        source_path = source_info_field(text, "dct:source")
        source_format = source_info_field(text, "dct:format")
        artifact_format = source_info_field(text, "fct:artifactFormat")
        if not graph_iri or triple_count_text is None or source_path is None or source_format is None or artifact_format is None:
            continue
        hdt_path = chunk_dir / "data.hdt"
        nt_path = chunk_dir / "data.nt"
        artifact_path = hdt_path if hdt_path.exists() else nt_path
        if not artifact_path.exists():
            continue
        entries[chunk_name] = MaterializedEntry(
            chunk_name=chunk_name,
            version=version,
            graph_iri=graph_iri,
            triple_count=int(triple_count_text),
            artifact_relpath=os.path.relpath(artifact_path, corpus_root),
            source_path=source_path,
            source_format=source_format,
            artifact_format=artifact_format,
        )
    return entries


def rebuild_toc_from_entries(
    corpus_root: Path,
    toc_dir: Path,
    dataset_name: str,
    entries: dict[str, MaterializedEntry],
    *,
    write_turtle: bool = False,
) -> Path:
    toc_graph = Graph()
    toc_graph.bind("dct", DCTERMS)
    toc_graph.bind("fct", FCT)
    for entry in sorted(entries.values(), key=lambda e: e.chunk_name):
        add_toc_entry(
            toc_graph,
            dataset_name,
            entry.graph_iri,
            entry.chunk_name,
            entry.version,
            entry.triple_count,
            entry.artifact_relpath,
            entry.source_path,
            entry.source_format,
            entry.artifact_format,
        )
    nt_path = toc_dir / "data.nt"
    toc_graph.serialize(destination=nt_path, format="nt", encoding="utf-8")
    if write_turtle:
        ttl_path = toc_dir / "data.ttl"
        toc_graph.serialize(destination=ttl_path, format="turtle")
    return nt_path


def import_line_rdf(args: argparse.Namespace) -> int:
    corpus_root = Path(args.corpus_root)
    toc_dir = corpus_root / "toc"
    ensure_dir(toc_dir)

    handles: dict[str, tuple[object, Path, str, int, str]] = {}
    source_path = str(Path(args.input).resolve())

    with open(args.input, "r", encoding="utf-8") as src:
        for line_no, line in enumerate(src, start=1):
            try:
                parsed = parse_nt_or_nq_line(line, args.input_format)
            except Exception as exc:
                raise RuntimeError(f"{args.input}:{line_no}: {exc}") from exc
            if parsed is None:
                continue

            graph_iri = parsed.graph_iri or args.default_graph_iri
            if not graph_iri:
                raise RuntimeError("default graph IRI required for N-Triples imports")

            if args.grouping == "graph":
                chunk_name = args.chunk_name or slugify(graph_iri)
                chunk_graph_iri = graph_iri
                artifact_name = "data.nt"
                line_text = parsed.triple_text + "\n"
            else:
                if args.input_format != "nq":
                    raise RuntimeError("bucket grouping currently requires N-Quads input")
                chunk_name = bucket_chunk_name(graph_iri, args.bucket_count)
                chunk_graph_iri = f"urn:factoidal:bucket:{args.dataset_name}:{chunk_name}"
                artifact_name = "data.nq"
                line_text = line.rstrip("\r\n") + "\n"
            if chunk_name not in handles:
                chunk_dir = corpus_root / chunk_name / args.version
                ensure_dir(chunk_dir)
                data_path = chunk_dir / artifact_name
                handle = open(data_path, "w", encoding="utf-8")
                handles[chunk_name] = (handle, chunk_dir, chunk_graph_iri, 0, artifact_name)

            handle, chunk_dir, chunk_graph_iri, count, artifact_name = handles[chunk_name]
            handle.write(line_text)
            handles[chunk_name] = (handle, chunk_dir, chunk_graph_iri, count + 1, artifact_name)

    entries: dict[str, MaterializedEntry] = {}

    for chunk_name, (handle, chunk_dir, graph_iri, count, artifact_name) in handles.items():
        handle.close()
        data_path = chunk_dir / artifact_name
        hdt_path = chunk_dir / "data.hdt"
        hdt_present = artifact_name == "data.nt" and maybe_build_hdt(args.hdt_command, data_path, hdt_path)
        source_format = "application/n-quads" if args.input_format == "nq" else "application/n-triples"
        artifact_format = (
            "application/vnd.hdt" if hdt_present else
            ("application/n-quads" if artifact_name == "data.nq" else "application/n-triples")
        )
        write_source_info(
            chunk_dir / "source-info.ttl",
            graph_iri,
            source_path,
            source_format,
            count,
            artifact_format,
        )
        artifact_relpath = os.path.relpath(hdt_path if hdt_present else data_path, corpus_root)
        entries[chunk_name] = MaterializedEntry(
            chunk_name=chunk_name,
            version=args.version,
            graph_iri=graph_iri,
            triple_count=count,
            artifact_relpath=artifact_relpath,
            source_path=source_path,
            source_format=source_format,
            artifact_format=artifact_format,
        )

    toc_path = rebuild_toc_from_entries(corpus_root, toc_dir, args.dataset_name, entries, write_turtle=False)
    print(f"corpus_root={corpus_root}")
    print(f"toc={toc_path}")
    print(f"chunks={len(entries)}")
    return 0


def partition_nq_by_graph(args: argparse.Namespace) -> int:
    input_path = Path(args.input)
    output_root = Path(args.output_root)
    ensure_dir(output_root)
    bucket_dir = output_root / "buckets"
    ensure_dir(bucket_dir)

    writers: dict[str, BucketWriter] = {}
    total_lines = 0
    total_bytes = 0
    total_graphs_seen = 0

    graph_manifest_path = output_root / "graph-bucket-map.tsv"
    bucket_manifest_path = output_root / "bucket-manifest.tsv"
    progress_path = output_root / "partition-progress.txt"
    seen_graphs: set[str] = set()

    with open(graph_manifest_path, "w", encoding="utf-8") as gm:
        gm.write("graph_iri\tbucket\n")

        with open(args.input, "r", encoding="utf-8") as src:
            for line_no, line in enumerate(src, start=1):
                try:
                    parsed = parse_nt_or_nq_line(line, "nq")
                except Exception as exc:
                    raise RuntimeError(f"{args.input}:{line_no}: {exc}") from exc
                if parsed is None:
                    continue

                if parsed.graph_iri is None:
                    raise RuntimeError(f"{args.input}:{line_no}: expected named graph in N-Quads input")

                graph_iri = parsed.graph_iri
                bucket_name = hash_bucket_name(graph_iri, args.bucket_count)
                if bucket_name not in writers:
                    bucket_path = bucket_dir / f"{bucket_name}.nq"
                    writers[bucket_name] = BucketWriter(
                        handle=open(bucket_path, "w", encoding="utf-8"),
                        line_count=0,
                        byte_count=0,
                    )

                writer = writers[bucket_name]
                payload = line.rstrip("\r\n") + "\n"
                payload_bytes = len(payload.encode("utf-8"))
                writer.handle.write(payload)
                writer.line_count += 1
                writer.byte_count += payload_bytes
                total_lines += 1
                total_bytes += payload_bytes

                if graph_iri not in seen_graphs:
                    seen_graphs.add(graph_iri)
                    total_graphs_seen += 1
                    gm.write(f"{graph_iri}\t{bucket_name}\n")

                if line_no % 100000 == 0:
                    gm.flush()
                    write_text(
                        progress_path,
                        "\n".join([
                            f"last_line={line_no}",
                            f"partitioned_lines={total_lines}",
                            f"partitioned_bytes={total_bytes}",
                            f"distinct_graphs={total_graphs_seen}",
                        ]) + "\n",
                    )

    for writer in writers.values():
        writer.handle.close()

    with open(bucket_manifest_path, "w", encoding="utf-8") as bm:
        bm.write("bucket\tlines\tbytes\n")
        for bucket_name in sorted(writers):
            writer = writers[bucket_name]
            bm.write(f"{bucket_name}\t{writer.line_count}\t{writer.byte_count}\n")

    summary_path = output_root / "partition-summary.txt"
    write_text(
        summary_path,
        "\n".join([
            f"input={input_path.resolve()}",
            f"input_bytes={input_path.stat().st_size}",
            f"partitioned_lines={total_lines}",
            f"partitioned_bytes={total_bytes}",
            f"distinct_graphs={total_graphs_seen}",
            f"bucket_count={args.bucket_count}",
            f"bucket_manifest={bucket_manifest_path}",
            f"graph_bucket_map={graph_manifest_path}",
        ]) + "\n",
    )
    if progress_path.exists():
        progress_path.unlink()

    print(f"output_root={output_root}")
    print(f"bucket_dir={bucket_dir}")
    print(f"bucket_count={args.bucket_count}")
    print(f"distinct_graphs={total_graphs_seen}")
    print(f"partitioned_lines={total_lines}")
    print(f"bucket_manifest={bucket_manifest_path}")
    print(f"graph_bucket_map={graph_manifest_path}")
    return 0


def shard_line_rdf(args: argparse.Namespace) -> int:
    output_dir = Path(args.output_dir)
    ensure_dir(output_dir)

    manifest = []
    shard_index = 0
    current_lines = []
    current_bytes = 0
    current_line_count = 0
    total_lines = 0

    def flush_current() -> None:
        nonlocal shard_index, current_lines, current_bytes, current_line_count
        if not current_lines:
            return
        shard_name = f"shard-{shard_index:05d}.{args.input_format}"
        shard_path = output_dir / shard_name
        with open(shard_path, "wb") as out:
          for line in current_lines:
            out.write(line)
        manifest.append((shard_name, current_line_count, current_bytes))
        shard_index += 1
        current_lines = []
        current_bytes = 0
        current_line_count = 0

    with open(args.input, "rb") as src:
        for raw_line in src:
            if not raw_line:
                continue
            line_len = len(raw_line)
            if current_lines and current_bytes + line_len > args.max_bytes:
                flush_current()
            current_lines.append(raw_line)
            current_bytes += line_len
            current_line_count += 1
            total_lines += 1

    flush_current()

    manifest_path = output_dir / "manifest.tsv"
    with open(manifest_path, "w", encoding="utf-8") as mf:
        mf.write("shard\tlines\tbytes\n")
        for shard_name, line_count, byte_count in manifest:
            mf.write(f"{shard_name}\t{line_count}\t{byte_count}\n")

    print(f"input={args.input}")
    print(f"output_dir={output_dir}")
    print(f"shards={len(manifest)}")
    print(f"lines={total_lines}")
    print(f"manifest={manifest_path}")
    return 0


def materialize_graph_hdt_corpus(args: argparse.Namespace) -> int:
    partition_root = Path(args.partition_root)
    bucket_dir = partition_root / "buckets"
    if not bucket_dir.exists():
        raise RuntimeError(f"missing bucket directory: {bucket_dir}")

    corpus_root = Path(args.corpus_root)
    toc_dir = corpus_root / "toc"
    ensure_dir(toc_dir)

    source_path = str(Path(args.input).resolve())
    progress_path = corpus_root / "materialize-progress.txt"
    error_log_path = corpus_root / "materialize-errors.log"
    write_materialize_progress(
        progress_path,
        phase="resume-scan",
        source=source_path,
        partition_root=partition_root,
        corpus_root=corpus_root,
        bucket_index=0,
        graph_count=0,
        triple_count=0,
    )
    entries = load_materialized_entries(corpus_root, args.version)
    graph_count = len(entries)
    triple_count = sum(entry.triple_count for entry in entries.values())
    bucket_index = 0
    write_materialize_progress(
        progress_path,
        phase="bucket-loop",
        source=source_path,
        partition_root=partition_root,
        corpus_root=corpus_root,
        resumed_graph_count=graph_count,
        resumed_triple_count=triple_count,
        bucket_index=0,
    )

    for bucket_path in sorted(bucket_dir.glob("bucket-*.nq")):
        bucket_index += 1
        write_materialize_progress(
            progress_path,
            phase="bucket-start",
            source=source_path,
            partition_root=partition_root,
            corpus_root=corpus_root,
            last_bucket=bucket_path.name,
            bucket_index=bucket_index,
            graph_count=graph_count,
            triple_count=triple_count,
        )
        handles: dict[str, tuple[object, Path, str, int]] = {}
        try:
            with open(bucket_path, "r", encoding="utf-8") as src:
                for line_no, line in enumerate(src, start=1):
                    try:
                        parsed = parse_nt_or_nq_line(line, "nq")
                    except Exception as exc:
                        append_text(error_log_path, f"PARSE\t{bucket_path}:{line_no}\t{exc}\n")
                        continue
                    if parsed is None:
                        continue
                    if parsed.graph_iri is None:
                        append_text(error_log_path, f"MISSING_GRAPH\t{bucket_path}:{line_no}\n")
                        continue

                    graph_iri = parsed.graph_iri
                    chunk_name = slugify(graph_iri)
                    if chunk_name in entries:
                        continue
                    if chunk_name not in handles:
                        chunk_dir = corpus_root / chunk_name / args.version
                        ensure_dir(chunk_dir)
                        nt_path = chunk_dir / "data.nt"
                        handle = open(nt_path, "w", encoding="utf-8")
                        handles[chunk_name] = (handle, chunk_dir, graph_iri, 0)

                    handle, chunk_dir, chunk_graph_iri, count = handles[chunk_name]
                    handle.write(parsed.triple_text + "\n")
                    handles[chunk_name] = (handle, chunk_dir, chunk_graph_iri, count + 1)
        finally:
            for handle, _, _, _ in handles.values():
                handle.close()

        for chunk_name, (_, chunk_dir, graph_iri, count) in handles.items():
            nt_path = chunk_dir / "data.nt"
            hdt_path = chunk_dir / "data.hdt"
            try:
                hdt_present = maybe_build_hdt(args.hdt_command, nt_path, hdt_path)
                artifact_format = "application/vnd.hdt" if hdt_present else "application/n-triples"
                write_source_info(
                    chunk_dir / "source-info.ttl",
                    graph_iri,
                    source_path,
                    "application/n-quads",
                    count,
                    artifact_format,
                )
                artifact_relpath = os.path.relpath(hdt_path if hdt_present else nt_path, corpus_root)
                entries[chunk_name] = MaterializedEntry(
                    chunk_name=chunk_name,
                    version=args.version,
                    graph_iri=graph_iri,
                    triple_count=count,
                    artifact_relpath=artifact_relpath,
                    source_path=source_path,
                    source_format="application/n-quads",
                    artifact_format=artifact_format,
                )
                graph_count += 1
                triple_count += count
            except Exception as exc:
                append_text(error_log_path, f"HDT\t{chunk_name}\t{graph_iri}\t{exc}\n")
                continue

        toc_path = toc_dir / "data.nt"
        write_materialize_progress(
            progress_path,
            phase="bucket-done",
            source=source_path,
            partition_root=partition_root,
            corpus_root=corpus_root,
            last_bucket=bucket_path.name,
            bucket_index=bucket_index,
            graph_count=len(entries),
            triple_count=sum(entry.triple_count for entry in entries.values()),
            toc=toc_path,
            toc_state="deferred",
        )

    toc_path = rebuild_toc_from_entries(corpus_root, toc_dir, args.dataset_name, entries, write_turtle=False)
    summary_path = corpus_root / "materialize-summary.txt"
    write_text(
        summary_path,
        "\n".join([
            f"partition_root={partition_root}",
            f"corpus_root={corpus_root}",
            f"graph_count={len(entries)}",
            f"triple_count={sum(entry.triple_count for entry in entries.values())}",
            f"toc={toc_path}",
            f"errors={error_log_path}",
        ]) + "\n",
    )
    write_materialize_progress(
        progress_path,
        phase="complete",
        source=source_path,
        partition_root=partition_root,
        corpus_root=corpus_root,
        bucket_index=bucket_index,
        graph_count=len(entries),
        triple_count=sum(entry.triple_count for entry in entries.values()),
        toc=toc_path,
        errors=error_log_path,
        summary=summary_path,
    )

    print(f"corpus_root={corpus_root}")
    print(f"graph_count={len(entries)}")
    print(f"triple_count={sum(entry.triple_count for entry in entries.values())}")
    print(f"toc={toc_path}")
    return 0


def materialize_nq_cottas_corpus(args: argparse.Namespace) -> int:
    corpus_root = Path(args.corpus_root)
    toc_dir = corpus_root / "toc"
    ensure_dir(toc_dir)

    chunk_name = args.chunk_name or slugify(args.dataset_name)
    chunk_dir = corpus_root / chunk_name / args.version
    ensure_dir(chunk_dir)

    data_nq_path = chunk_dir / "data.nq"
    cottas_path = chunk_dir / "data.cottas"
    factbin_path = chunk_dir / "data.factbin"
    summary_path = chunk_dir / "summary.json"

    graph_values: set[str] = set()
    quad_count = 0
    parsed_rows: list[ParsedLine] = []

    with open(args.input, "r", encoding="utf-8") as src, data_nq_path.open("w", encoding="utf-8") as data_out:
        for line_no, line in enumerate(src, start=1):
            try:
                parsed = parse_nt_or_nq_line(line, "nq")
            except Exception as exc:
                raise RuntimeError(f"{args.input}:{line_no}: {exc}") from exc
            if parsed is None:
                continue

            data_out.write(line.rstrip("\r\n") + "\n")
            parsed_rows.append(parsed)
            if parsed.graph_iri is not None:
                graph_values.add(parsed.graph_iri)
            quad_count += 1

    write_factbin(factbin_path, parsed_rows)

    try:
        import pycottas
    except ImportError as exc:
        raise RuntimeError(
            "pycottas is required for true COTTAS output; install it and rerun"
        ) from exc

    pycottas.rdf2cottas(str(data_nq_path), str(cottas_path), index=args.index, disk=args.disk)
    verified = pycottas.verify(str(cottas_path))
    info = pycottas.info(str(cottas_path))

    summary = {
        "artifact_type": "pycottas-cottas",
        "source_path": str(Path(args.input).resolve()),
        "source_format": "application/n-quads",
        "dataset_name": args.dataset_name,
        "version": args.version,
        "quad_count": quad_count,
        "graph_count": len(graph_values),
        "index": args.index.lower(),
        "verified": verified,
        "cottas_info": info,
        "files": {
            "data_cottas": "data.cottas",
            "data_factbin": "data.factbin",
            "data_nq": "data.nq",
        },
    }
    write_text(summary_path, json.dumps(summary, indent=2) + "\n")

    source_path = str(Path(args.input).resolve())
    dataset_iri = args.dataset_iri or f"urn:factoidal:dataset:{args.dataset_name}"
    write_source_info(
        chunk_dir / "source-info.ttl",
        dataset_iri,
        source_path,
        "application/n-quads",
        quad_count,
        "application/vnd.cottas",
    )

    entries = {
        chunk_name: MaterializedEntry(
            chunk_name=chunk_name,
            version=args.version,
            graph_iri=dataset_iri,
            triple_count=quad_count,
            artifact_relpath=os.path.relpath(cottas_path, corpus_root),
            source_path=source_path,
            source_format="application/n-quads",
            artifact_format="application/vnd.cottas",
        )
    }

    toc_path = rebuild_toc_from_entries(corpus_root, toc_dir, args.dataset_name, entries, write_turtle=False)
    print(f"corpus_root={corpus_root}")
    print(f"chunk={chunk_name}")
    print(f"artifact={cottas_path}")
    print(f"quads={quad_count}")
    print(f"graphs={len(graph_values)}")
    print(f"verified={verified}")
    print(f"toc={toc_path}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Build a Corpus/ tree from line-oriented RDF inputs.")
    sub = parser.add_subparsers(dest="cmd", required=True)

    import_parser = sub.add_parser("import-line-rdf", help="Import N-Triples or N-Quads into Corpus/ layout.")
    import_parser.add_argument("--input", required=True, help="Input .nt or .nq file")
    import_parser.add_argument("--input-format", choices=["nt", "nq"], required=True)
    import_parser.add_argument("--corpus-root", default="Corpus")
    import_parser.add_argument("--dataset-name", required=True, help="Logical dataset identifier for TOC IRIs")
    import_parser.add_argument("--chunk-name", help="Optional stable directory name for single-graph imports")
    import_parser.add_argument("--grouping", choices=["graph", "bucket"], default="graph", help="Chunking policy for imports")
    import_parser.add_argument("--bucket-count", type=int, default=256, help="Bucket count when --grouping bucket is used")
    import_parser.add_argument("--version", default="v1")
    import_parser.add_argument("--default-graph-iri", help="IRI to assign when importing N-Triples")
    import_parser.add_argument("--hdt-command", default="rdf2hdt", help="External HDT builder command; skipped if unavailable")
    import_parser.set_defaults(func=import_line_rdf)

    shard_parser = sub.add_parser("shard-line-rdf", help="Split N-Triples or N-Quads into line-safe shards.")
    shard_parser.add_argument("--input", required=True, help="Input .nt or .nq file")
    shard_parser.add_argument("--input-format", choices=["nt", "nq"], required=True)
    shard_parser.add_argument("--output-dir", required=True)
    shard_parser.add_argument("--max-bytes", type=int, default=134217728, help="Maximum bytes per shard, default 128 MiB")
    shard_parser.set_defaults(func=shard_line_rdf)

    partition_parser = sub.add_parser("partition-nq-graphs", help="Partition a full N-Quads file into graph-hash buckets with manifests.")
    partition_parser.add_argument("--input", required=True, help="Input .nq file")
    partition_parser.add_argument("--output-root", required=True)
    partition_parser.add_argument("--bucket-count", type=int, default=4096)
    partition_parser.set_defaults(func=partition_nq_by_graph)

    materialize_parser = sub.add_parser("materialize-graph-hdt-corpus", help="Materialize one folder per named graph and optional HDT from a partitioned N-Quads bucket set.")
    materialize_parser.add_argument("--input", required=True, help="Original source .nq file, used for provenance")
    materialize_parser.add_argument("--partition-root", required=True)
    materialize_parser.add_argument("--corpus-root", required=True)
    materialize_parser.add_argument("--dataset-name", required=True)
    materialize_parser.add_argument("--version", default="v1")
    materialize_parser.add_argument("--hdt-command", default="rdf2hdt", help="External HDT builder command; skipped if unavailable")
    materialize_parser.set_defaults(func=materialize_graph_hdt_corpus)

    cottas_parser = sub.add_parser("materialize-nq-cottas-corpus", help="Materialize a single dataset-level COTTAS-style artifact directory from an N-Quads file.")
    cottas_parser.add_argument("--input", required=True, help="Input .nq file")
    cottas_parser.add_argument("--corpus-root", required=True)
    cottas_parser.add_argument("--dataset-name", required=True)
    cottas_parser.add_argument("--chunk-name", help="Optional stable directory name for the dataset artifact")
    cottas_parser.add_argument("--dataset-iri", help="Optional synthetic dataset IRI for TOC/source-info metadata")
    cottas_parser.add_argument("--index", default="spog", help="COTTAS index permutation, e.g. spo or spog")
    cottas_parser.add_argument("--disk", action="store_true", help="Use a disk-backed DuckDB database during pycottas conversion")
    cottas_parser.add_argument("--version", default="v1")
    cottas_parser.set_defaults(func=materialize_nq_cottas_corpus)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
