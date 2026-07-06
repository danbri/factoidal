#!/usr/bin/env python3

import argparse
import hashlib
import json
import os
import random
import re
import shlex
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


# ----------------------------------------------------------------------
# Format detection + non-line-based RDF → N-Quads conversion
#
# The line-based pipeline below (parse_nt_or_nq_line, write_factbin,
# materialize-nq-cottas-corpus, etc.) expects N-Triples or N-Quads on
# disk. For block-structured formats (TriG, Turtle, RDF/XML) we
# pre-convert to N-Quads first. Prefer pyoxigraph's streaming parser
# when present; fall back to rdflib when it is not. The conversion
# writes quads one per line, so callers can feed the resulting file
# through the same `.nq` pipeline without touching inner logic.
#
# Graph IRIs: quads from non-default contexts carry `<g>` as the 4th
# term; default-graph triples omit the graph term (empty = default).
# This matches the interning convention in write_factbin (graph id 0
# = default).
# ----------------------------------------------------------------------

RDF_FORMAT_BY_EXT: dict[str, str] = {
    ".nq": "nq",
    ".nquads": "nq",
    ".nt": "nt",
    ".ntriples": "nt",
    ".trig": "trig",
    ".ttl": "turtle",
    ".turtle": "turtle",
    ".rdf": "rdfxml",
    ".xml": "rdfxml",
    ".owl": "rdfxml",
}


def detect_platform_tag() -> str:
    if sys.platform == "darwin" and os.uname().machine == "arm64":
        return "darwin-arm64"
    if sys.platform == "darwin" and os.uname().machine == "x86_64":
        return "darwin-x86_64"
    if sys.platform.startswith("linux") and os.uname().machine == "x86_64":
        return "linux-x86_64"
    if sys.platform.startswith("linux") and os.uname().machine in ("aarch64", "arm64"):
        return "linux-arm64"
    return f"{sys.platform}-{os.uname().machine}"


def infer_rdf_format(path: Path) -> str:
    return RDF_FORMAT_BY_EXT.get(path.suffix.lower(), "")


def resolve_factoidal_bin() -> str:
    env_bin = os.environ.get("FACTOIDAL_BIN")
    if env_bin:
        return env_bin
    repo_root = Path(__file__).resolve().parent.parent
    bindir = repo_root / "bin" / detect_platform_tag()
    for name in ("factoidal-dump-nq.byte", "factoidal-dump-nq", "factoidal", "factoidal.byte"):
        candidate = bindir / name
        if candidate.exists():
            return str(candidate)
    found = shutil.which("factoidal")
    if found:
        return found
    raise RuntimeError(
        "Factoidal parser requested, but no factoidal binary was found. "
        "Set FACTOIDAL_BIN=/path/to/factoidal(-dump-nq) or build bin/<platform>/factoidal-dump-nq.byte."
    )


def _nt_escape_literal_lex(value: str) -> str:
    # N-Triples/N-Quads literal lexical escape per the 2014 grammar:
    # only \\, \", \n, \r, \t are allowed; all other control chars
    # must be escaped as \uXXXX. rdflib's .n3() may use triple-quoted
    # Turtle syntax (""") for literals with newlines, which is NOT
    # valid N-Quads — so build our own.
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
    # Emit URIRef / BNode / Literal in strict N-Triples/N-Quads syntax.
    # Avoid rdflib .n3() for Literals because it may produce Turtle-only
    # triple-quoted (""") strings that our internal parser rejects.
    # Classes are resolved by duck-typing to avoid a hard rdflib import.
    cls_name = type(term).__name__
    if cls_name == "URIRef":
        return f"<{str(term)}>"
    if cls_name == "BNode":
        return f"_:{str(term)}"
    if cls_name == "Literal":
        lex = _nt_escape_literal_lex(str(term))
        lang = getattr(term, "language", None)
        dt = getattr(term, "datatype", None)
        if lang:
            return f"\"{lex}\"@{lang}"
        if dt is not None:
            return f"\"{lex}\"^^<{str(dt)}>"
        return f"\"{lex}\""
    # Fallback: stringify in angle brackets (URI-like).
    return f"<{str(term)}>"


def _nquads_line_for(triple, graph) -> str:
    s, p, o = triple
    if graph is None:
        return f"{_nt_term(s)} {_nt_term(p)} {_nt_term(o)} ."
    ident = getattr(graph, "identifier", graph)
    ident_str = str(ident)
    if ident_str == "urn:x-rdflib:default" or ident_str == "":
        return f"{_nt_term(s)} {_nt_term(p)} {_nt_term(o)} ."
    # Graph identifier may be URIRef or BNode.
    return f"{_nt_term(s)} {_nt_term(p)} {_nt_term(o)} {_nt_term(ident)} ."


def _pyoxigraph_term(term) -> str:
    cls_name = type(term).__name__
    if cls_name == "NamedNode":
        return f"<{term.value}>"
    if cls_name == "BlankNode":
        return f"_:{term.value}"
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


def convert_rdf_to_nquads_pyoxigraph(input_path: Path, input_format: str, output_nq_path: Path) -> int:
    try:
        from pyoxigraph import parse
    except ImportError as exc:
        raise RuntimeError(
            "pyoxigraph is required for streaming RDF conversion; install it or use the rdflib fallback."
        ) from exc

    mime_by_format = {
        "trig": "application/trig",
        "turtle": "text/turtle",
        "rdfxml": "application/rdf+xml",
        "nt": "application/n-triples",
        "nq": "application/n-quads",
    }
    mime = mime_by_format[input_format]
    quad_count = 0
    with input_path.open("rb") as src, output_nq_path.open("w", encoding="utf-8") as out:
        for item in parse(src, mime):
            subject = _pyoxigraph_term(item.subject)
            predicate = _pyoxigraph_term(item.predicate)
            obj = _pyoxigraph_term(item.object)
            graph_name = getattr(item, "graph_name", None)
            if graph_name is None or str(graph_name) == "DEFAULT":
                out.write(f"{subject} {predicate} {obj} .\n")
            else:
                out.write(f"{subject} {predicate} {obj} {_pyoxigraph_term(graph_name)} .\n")
            quad_count += 1
    return quad_count


def convert_rdf_to_nquads_factoidal(input_path: Path, input_format: str, output_nq_path: Path) -> int:
    factoidal_bin = resolve_factoidal_bin()
    bin_name = os.path.basename(factoidal_bin)
    if bin_name.startswith("factoidal-dump-nq"):
        cmd = [factoidal_bin, "--format", input_format, str(input_path)]
    else:
        cmd = [factoidal_bin, "--dump-nq", "--format", input_format, str(input_path)]
    try:
        with output_nq_path.open("w", encoding="utf-8") as out:
            subprocess.run(cmd, check=True, stdout=out)
    except subprocess.CalledProcessError as exc:
        pretty = " ".join(shlex.quote(part) for part in cmd)
        raise RuntimeError(f"Factoidal dump-nq failed: {pretty}") from exc

    quad_count = 0
    with output_nq_path.open("r", encoding="utf-8") as src:
        for line in src:
            if line.strip() and not line.lstrip().startswith("#"):
                quad_count += 1
    return quad_count


def convert_rdf_to_nquads_rdflib(input_path: Path, input_format: str, output_nq_path: Path) -> int:
    """Parse an RDF file and emit a line-per-quad .nq file at
    `output_nq_path`. Returns the quad count.

    For TriG/N-Quads multi-graph inputs, named-graph context is
    preserved. For single-graph inputs (Turtle/N-Triples/RDF/XML),
    triples go to the default graph (empty 4th column). Prefer the
    pyoxigraph streaming parser; fall back to rdflib if pyoxigraph is
    unavailable.
    """
    try:
        from rdflib import Dataset, Graph
    except ImportError as exc:
        raise RuntimeError(
            "rdflib is required to ingest non-line RDF formats (trig/turtle/rdfxml). "
            "Install with: pip install rdflib"
        ) from exc

    if input_format == "trig":
        ds = Dataset()
        ds.parse(str(input_path), format="trig")
        quad_count = 0
        with output_nq_path.open("w", encoding="utf-8") as out:
            for s, p, o, g in ds.quads((None, None, None, None)):
                out.write(_nquads_line_for((s, p, o), g) + "\n")
                quad_count += 1
        return quad_count

    if input_format in ("turtle", "rdfxml", "nt"):
        rdflib_fmt = {"turtle": "turtle", "rdfxml": "xml", "nt": "nt"}[input_format]
        g = Graph()
        g.parse(str(input_path), format=rdflib_fmt)
        quad_count = 0
        with output_nq_path.open("w", encoding="utf-8") as out:
            for s, p, o in g:
                out.write(_nquads_line_for((s, p, o), None) + "\n")
                quad_count += 1
        return quad_count

    if input_format == "nq":
        # Passthrough; caller should skip conversion. Return line count.
        with output_nq_path.open("w", encoding="utf-8") as out:
            with input_path.open("r", encoding="utf-8") as src:
                quad_count = 0
                for line in src:
                    if line.strip() and not line.lstrip().startswith("#"):
                        out.write(line)
                        quad_count += 1
        return quad_count

    raise ValueError(f"Unsupported input format: {input_format}")


def convert_rdf_to_nquads(
    input_path: Path,
    input_format: str,
    output_nq_path: Path,
    parser_name: str,
) -> tuple[int, str]:
    if input_format == "nq":
        with output_nq_path.open("w", encoding="utf-8") as out:
            with input_path.open("r", encoding="utf-8") as src:
                quad_count = 0
                for line in src:
                    if line.strip() and not line.lstrip().startswith("#"):
                        out.write(line)
                        quad_count += 1
        return quad_count, "passthrough"

    if parser_name == "factoidal":
        return convert_rdf_to_nquads_factoidal(input_path, input_format, output_nq_path), "factoidal"
    if parser_name == "pyoxigraph":
        return convert_rdf_to_nquads_pyoxigraph(input_path, input_format, output_nq_path), "pyoxigraph"
    if parser_name == "rdflib":
        return convert_rdf_to_nquads_rdflib(input_path, input_format, output_nq_path), "rdflib"
    if parser_name == "python":
        try:
            return convert_rdf_to_nquads_pyoxigraph(input_path, input_format, output_nq_path), "pyoxigraph"
        except ImportError:
            return convert_rdf_to_nquads_rdflib(input_path, input_format, output_nq_path), "rdflib"
    if parser_name == "auto":
        try:
            return convert_rdf_to_nquads_factoidal(input_path, input_format, output_nq_path), "factoidal"
        except Exception:
            try:
                return convert_rdf_to_nquads_pyoxigraph(input_path, input_format, output_nq_path), "pyoxigraph"
            except ImportError:
                return convert_rdf_to_nquads_rdflib(input_path, input_format, output_nq_path), "rdflib"
    raise ValueError(f"Unsupported parser selection: {parser_name}")


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


def resolve_factoidal_query_bin() -> str:
    """Locate the main `factoidal` CLI binary (the one with `query`,
    `--data-cottas`, `--explain`) -- distinct from resolve_factoidal_bin()
    above, which prefers the `-dump-nq` front end for RDF-to-N-Quads
    conversion. Sidecar-at-import (build_cottas_sidecars_eager below)
    specifically needs the query binary, because that is the one whose
    `--explain` path opens the COTTAS store and pre-warms the on-disk
    companion indexes."""
    env_bin = os.environ.get("FACTOIDAL_QUERY_BIN")
    if env_bin:
        return env_bin
    repo_root = Path(__file__).resolve().parent.parent
    bindir = repo_root / "bin" / detect_platform_tag()
    candidate = bindir / "factoidal"
    if candidate.exists():
        return str(candidate)
    found = shutil.which("factoidal")
    if found:
        return found
    raise RuntimeError(
        "factoidal query binary not found; set FACTOIDAL_QUERY_BIN=/path/to/factoidal "
        "or build bin/<platform>/factoidal."
    )


# Companion sidecar file suffixes written by
# RDF_CottasStore.Cottas_companion_writer / Cottas_compound_po_writer
# (formal/fstar/experimental_ocaml_glue/cottas_ondisk_z*.sh), one .dict +
# .presence pair per column (s, p, o, g), plus the Lamed3 predicate
# offsets index and the compound (p,o) presence bitmap.
COTTAS_SIDECAR_SUFFIXES = [
    ".s.dict", ".s.presence",
    ".p.dict", ".p.presence",
    ".o.dict", ".o.presence",
    ".g.dict", ".g.presence",
    ".p.offsets",
    ".po.presence",
]


def build_cottas_sidecars_eager(cottas_path: Path) -> list[str]:
    """Force-build the .dict/.presence/.offsets/.po.presence companion
    sidecars next to `cottas_path` at import time, instead of leaving
    them to be built lazily the first time a server (factoidal-http)
    opens the store (docs/designissues/2026-07-05-disk-backed-db-perf-
    review.md §1.2/§3 item 5).

    Rule-#11 / anti-pattern-#4 note: the sidecar *writer* logic lives in
    OCaml glue patched into RDF_CottasStore.ml (Cottas_companion_writer,
    Cottas_companion_boot.prewarm_via_companions, Cottas_compound_po_writer
    -- formal/fstar/experimental_ocaml_glue/cottas_ondisk_z*.sh) and is
    already wired into two binaries: factoidal-http (server boot,
    bin/factoidal-http/factoidal_http.ml:prewarm_cottas_columns) and the
    main `factoidal` CLI's `--explain` mode
    (bin/factoidal-explain/factoidal_explain.ml:explain_query, which calls
    `cottas_ondisk_open` then `Cottas_companion_boot.prewarm_via_companions`
    before printing a plan, specifically so the explain path itself isn't
    paying a cold-start tax). Rather than reimplementing that walk in
    Python, this function shells out to
    `factoidal query --data-cottas <path> --explain '<trivial query>'` --
    prewarm runs as a side effect of opening the store for the explain
    path, and the companions are written to *disk* (not just populated as
    in-memory Hashtbls) because prewarm_via_companions calls
    build_companion_pair / build_offsets_file / build_compound_po_file
    whenever the corresponding sidecar file is absent. The explain text
    output is discarded; only the on-disk side effect (the sidecar files)
    is wanted. No new OCaml logic is added by this function.
    """
    factoidal_bin = resolve_factoidal_query_bin()
    trivial_query = "SELECT * WHERE { ?s ?p ?o } LIMIT 1"
    cmd = [
        factoidal_bin, "query",
        "--data-cottas", str(cottas_path),
        "--explain", trivial_query,
    ]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=570)
    if result.returncode != 0:
        pretty = " ".join(shlex.quote(part) for part in cmd)
        raise RuntimeError(
            f"Sidecar-build via --explain failed (rc={result.returncode}): {pretty}\n"
            f"stderr:\n{result.stderr}"
        )
    return [
        suffix for suffix in COTTAS_SIDECAR_SUFFIXES
        if Path(str(cottas_path) + suffix).exists()
    ]


def write_cottas_clustered(
    nq_path: Path,
    cottas_path: Path,
    row_group_size: int,
    index_label: str = "cs",
) -> None:
    """Write a COTTAS/Parquet file that preserves the row order of
    `nq_path` exactly, instead of pycottas.rdf2cottas's behaviour of
    always re-sorting rows by the `index` permutation's column letters
    (pycottas 1.1.0 `__init__.py` `rdf2cottas`: `ORDER BY <index chars>`,
    which cannot preserve a producer-chosen order -- see
    docs/designissues/2026-07-03-e1-cs-clustering-results.md §1). Used
    for the characteristic-set-clustered row order (`--row-order cs`):
    the caller pre-sorts `nq_path` (tools/cs_cluster_nq.py) by
    `(CS(s), s, p, o, g)` and this function must not re-sort it.

    Mirrors rdf2cottas's schema, DISTINCT-quad dedup semantics, and
    Parquet write options (ZSTD level 22, PARQUET_VERSION v2,
    KV_METADATA) with two deltas: (1) a `seq` column carries the
    pre-sorted row position through a GROUP BY-based dedupe (DISTINCT
    alone does not guarantee output order matches input order), and
    (2) ROW_GROUP_SIZE is passed explicitly instead of left at DuckDB's
    122,880-row default, since the whole point of this ordering is to
    give the row-group prune cascade (Yod6/Tet3/Lamed3/compound-po)
    smaller, CS-homogeneous groups to skip.
    """
    import duckdb
    import pyoxigraph

    con = duckdb.connect(":memory:")
    con.execute("SET preserve_insertion_order = false; SET enable_progress_bar = false;")
    con.execute(
        "CREATE TABLE quads (seq BIGINT, s VARCHAR NOT NULL, p VARCHAR NOT NULL, "
        "o VARCHAR NOT NULL, g VARCHAR)"
    )

    def flush(rows: list[list[str]], seqs: list[int]) -> None:
        if not rows:
            return
        import pandas as pd
        df = pd.DataFrame.from_records(rows, columns=["st", "pt", "ot", "gt"])
        df.insert(0, "seqt", seqs)
        table = f"tmp_quads_{random.randint(0, 1_000_000)}"
        con.register(table, df)
        con.execute(f"INSERT INTO quads (SELECT seqt, st, pt, ot, gt FROM {table})")
        con.unregister(table)

    rows: list[list[str]] = []
    seqs: list[int] = []
    seq = 0
    for quad in pyoxigraph.parse(str(nq_path), base_iri=None, mime_type="application/n-quads"):
        rows.append([str(term) for term in quad])
        seqs.append(seq)
        seq += 1
        if len(rows) >= 1_000_000:
            flush(rows, seqs)
            rows, seqs = [], []
    flush(rows, seqs)

    export_query = (
        "COPY (SELECT s, p, o, g FROM ("
        "  SELECT s, p, o, g, MIN(seq) AS first_seq FROM quads GROUP BY s, p, o, g"
        ") ORDER BY first_seq) "
        f"TO '{cottas_path}' (FORMAT PARQUET, COMPRESSION ZSTD, COMPRESSION_LEVEL 22, "
        f"PARQUET_VERSION v2, ROW_GROUP_SIZE {int(row_group_size)}, "
        f"KV_METADATA {{index: '{index_label}'}})"
    )
    con.execute(export_query)


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

    input_path = Path(args.input)
    # Resolve input format: explicit flag wins, else infer from extension.
    input_format = getattr(args, "input_format", "") or infer_rdf_format(input_path)
    if not input_format:
        raise RuntimeError(
            f"Cannot infer RDF format for {args.input}; pass --input-format "
            "(one of nq, nt, trig, turtle, rdfxml)"
        )

    parser_name = getattr(args, "parser", "factoidal")
    if input_format in ("trig", "turtle", "rdfxml", "nt"):
        print(
            f"Pre-converting {input_format} → N-Quads via parser={parser_name} …",
            file=sys.stderr,
        )
        converted_count, parser_used = convert_rdf_to_nquads(
            input_path,
            input_format,
            data_nq_path,
            parser_name,
        )
        print(
            f"  parser={parser_used} wrote {converted_count} quads to {data_nq_path}",
            file=sys.stderr,
        )
        nq_input_path = data_nq_path
    else:
        converted_count, parser_used = convert_rdf_to_nquads(
            input_path,
            input_format,
            data_nq_path,
            parser_name,
        )
        print(
            f"Normalising {input_format} via parser={parser_used} …",
            file=sys.stderr,
        )
        nq_input_path = data_nq_path

    graph_values: set[str] = set()
    quad_count = 0
    parsed_rows: list[ParsedLine] = []

    # When nq_input_path is the pre-converted data.nq file inside
    # chunk_dir, we read from it and DON'T rewrite it (open the same
    # path for writing would truncate).
    writing_passthrough = nq_input_path != data_nq_path
    data_out = data_nq_path.open("w", encoding="utf-8") if writing_passthrough else None
    try:
        with nq_input_path.open("r", encoding="utf-8") as src:
            for line_no, line in enumerate(src, start=1):
                try:
                    parsed = parse_nt_or_nq_line(line, "nq")
                except Exception as exc:
                    raise RuntimeError(f"{nq_input_path}:{line_no}: {exc}") from exc
                if parsed is None:
                    continue

                if data_out is not None:
                    data_out.write(line.rstrip("\r\n") + "\n")
                parsed_rows.append(parsed)
                if parsed.graph_iri is not None:
                    graph_values.add(parsed.graph_iri)
                quad_count += 1
    finally:
        if data_out is not None:
            data_out.close()

    write_factbin(factbin_path, parsed_rows)

    row_order = getattr(args, "row_order", "producer")
    # Default matches DuckDB's own default (pycottas.rdf2cottas leaves
    # ROW_GROUP_SIZE unset, so DuckDB picks 122,880) rather than a smaller
    # value. Measured on the gene corpus (2026-07-05,
    # docs/designissues/2026-07-05-disk-backed-db-perf-review.md roadmap
    # item 3): shrinking to 20,000 rows/group (44 groups instead of 8)
    # made every query ~24x SLOWER (73ms -> 1.88s for the same query),
    # not faster -- the current on-disk reader pays a per-row-group cost
    # that scales worse than linearly with row-group count on this
    # corpus size, which swamps any prune-selectivity gain from more/
    # smaller groups.
    #
    # Follow-up (2026-07-05, same doc, item 2): characterised and
    # PARTIALLY fixed. The dominant re-hex-encoding-the-footer-per-probe
    # cost is now memoized (OCaml I/O glue, Parquet_Footer.ml's Mim3
    # cache) -- ~23% faster at 44 groups on gene (1.88s -> ~1.45s) -- but
    # a second, larger cost remained (an O(row_groups) structural walk
    # inside Parquet.Footer.fst itself).
    #
    # Follow-up (2026-07-06, same doc, item 2 DONE): that second cost is
    # now closed in F* (row-group-offset table built once per query,
    # Parquet.Footer.probe_parquet_row_group_offset_table + the
    # _from_table probe family). 44 groups on gene is now 83-84ms vs
    # 20ms at 8 groups on the universal-predicate query (was ~1.45s vs
    # 62-63ms) -- the quadratic component is gone; the residual ~4x is
    # linear per-row-group planner cost. Re-measured with the fix in:
    # the rare/shape-confined predicate query is STILL slower at 44
    # groups (84-85ms) than at the default 8 (28-29ms), so smaller row
    # groups still lose on this corpus and --row-group-size keeps
    # DuckDB's own default. Revisit after a cross-query dict cache
    # (Tsade2 Phase E) or against parliament's 232-predicate shape.
    row_group_size = getattr(args, "row_group_size", None) or 122880

    try:
        import pycottas
    except ImportError as exc:
        raise RuntimeError(
            "pycottas is required for true COTTAS output; install it and rerun"
        ) from exc

    if row_order == "cs":
        # Characteristic-set row clustering (E1,
        # docs/designissues/2026-07-03-shapes-canon-storage-strategies.md
        # §5, results in
        # docs/designissues/2026-07-03-e1-cs-clustering-results.md, wired
        # into this pipeline per
        # docs/designissues/2026-07-05-disk-backed-db-perf-review.md
        # roadmap item 3). pycottas.rdf2cottas cannot preserve a
        # producer-chosen row order (it always re-sorts by the `index`
        # permutation's columns), so re-order data.nq via
        # tools/cs_cluster_nq.py and write the Parquet ourselves with
        # write_cottas_clustered, which mirrors rdf2cottas's schema/
        # dedup/compression settings but keeps the clustered row order.
        clustered_nq_path = chunk_dir / "data.cs-clustered.nq"
        cluster_stats_path = chunk_dir / "cs-cluster-stats.log"
        cluster_cmd = [
            sys.executable,
            str(Path(__file__).resolve().parent / "cs_cluster_nq.py"),
            "--stats",
            str(data_nq_path),
        ]
        print(f"Clustering rows by characteristic set of subject: {' '.join(cluster_cmd)}", file=sys.stderr)
        with clustered_nq_path.open("w", encoding="utf-8") as out:
            cluster_result = subprocess.run(cluster_cmd, stdout=out, stderr=subprocess.PIPE, text=True, timeout=570)
        write_text(cluster_stats_path, cluster_result.stderr)
        if cluster_result.returncode != 0:
            raise RuntimeError(
                f"cs_cluster_nq.py failed (rc={cluster_result.returncode}): {cluster_result.stderr}"
            )
        print(cluster_result.stderr, file=sys.stderr)
        write_cottas_clustered(clustered_nq_path, cottas_path, row_group_size, index_label="cs")
    else:
        pycottas.rdf2cottas(str(data_nq_path), str(cottas_path), index=args.index, disk=args.disk)

    verified = pycottas.verify(str(cottas_path))
    info = pycottas.info(str(cottas_path))

    sidecars_built: list[str] = []
    if getattr(args, "build_sidecars", False):
        print(f"Building COTTAS sidecars eagerly at import time for {cottas_path} …", file=sys.stderr)
        sidecars_built = build_cottas_sidecars_eager(cottas_path)
        print(f"  sidecars present: {sidecars_built}", file=sys.stderr)

    mime_by_format = {
        "nq": "application/n-quads",
        "nt": "application/n-triples",
        "trig": "application/trig",
        "turtle": "text/turtle",
        "rdfxml": "application/rdf+xml",
    }
    source_mime = mime_by_format.get(input_format, "application/n-quads")
    summary = {
        "artifact_type": "pycottas-cottas",
        "source_path": str(Path(args.input).resolve()),
        "source_format": source_mime,
        "dataset_name": args.dataset_name,
        "version": args.version,
        "parser_requested": parser_name,
        "parser_used": parser_used,
        "quad_count": quad_count,
        "graph_count": len(graph_values),
        "index": args.index.lower(),
        "row_order": row_order,
        "row_group_size": row_group_size if row_order == "cs" else None,
        "sidecars_built": sidecars_built,
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
        source_mime,
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
            source_format=source_mime,
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
    print(f"row_order={row_order}")
    print(f"sidecars_built={sidecars_built}")
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

    cottas_parser = sub.add_parser(
        "materialize-nq-cottas-corpus",
        help="Materialize a dataset-level COTTAS artifact from any supported RDF input (nq/nt/trig/turtle/rdfxml).",
    )
    cottas_parser.add_argument("--input", required=True, help="Input RDF file (auto-detected by extension)")
    cottas_parser.add_argument(
        "--input-format",
        choices=["nq", "nt", "trig", "turtle", "rdfxml"],
        default="",
        help="Override format inferred from file extension",
    )
    cottas_parser.add_argument("--corpus-root", required=True)
    cottas_parser.add_argument("--dataset-name", required=True)
    cottas_parser.add_argument("--chunk-name", help="Optional stable directory name for the dataset artifact")
    cottas_parser.add_argument("--dataset-iri", help="Optional synthetic dataset IRI for TOC/source-info metadata")
    cottas_parser.add_argument(
        "--parser",
        choices=["factoidal", "auto", "python", "pyoxigraph", "rdflib"],
        default="factoidal",
        help=(
            "RDF parser/serializer front end for non-.nq inputs. "
            "factoidal uses the local factoidal binary's canonical N-Quads dump; "
            "python prefers pyoxigraph and falls back to rdflib; auto tries factoidal first."
        ),
    )
    cottas_parser.add_argument("--index", default="spog", help="COTTAS index permutation, e.g. spo or spog (used when --row-order producer)")
    cottas_parser.add_argument("--disk", action="store_true", help="Use a disk-backed DuckDB database during pycottas conversion")
    cottas_parser.add_argument("--version", default="v1")
    cottas_parser.add_argument(
        "--row-order",
        choices=["producer", "cs"],
        default="producer",
        help=(
            "producer (default): unchanged behaviour, pycottas.rdf2cottas sorts by "
            "--index's column letters. cs: cluster rows by (characteristic-set-of-"
            "subject, s, p, o, g) via tools/cs_cluster_nq.py before writing, so the "
            "row-group prune cascade (Yod6/Tet3/Lamed3/compound-po) gets predicate-"
            "homogeneous row groups instead of every predicate spread across every "
            "group (docs/designissues/2026-07-05-disk-backed-db-perf-review.md "
            "roadmap item 3; experiment writeup in "
            "docs/designissues/2026-07-03-e1-cs-clustering-results.md)."
        ),
    )
    cottas_parser.add_argument(
        "--row-group-size",
        type=int,
        default=None,
        help=(
            "Parquet ROW_GROUP_SIZE (rows/group) when --row-order cs. Defaults to "
            "DuckDB's own default (122880) if unset -- measured smaller values "
            "regress query latency on the current reader (see corpus_pipeline.py "
            "materialize_nq_cottas_corpus comment); only override this if you have "
            "measured the effect on your corpus."
        ),
    )
    cottas_parser.add_argument(
        "--build-sidecars",
        action="store_true",
        help=(
            "Eagerly build the .dict/.presence/.p.offsets/.po.presence companion "
            "sidecars right after writing data.cottas, instead of leaving them to "
            "be built lazily the first time a server opens the store. Invokes the "
            "existing factoidal --explain prewarm path (no new OCaml logic)."
        ),
    )
    cottas_parser.set_defaults(func=materialize_nq_cottas_corpus)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
