#!/usr/bin/env python3

import argparse
import os
import statistics
import subprocess
import tempfile
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
FACTOIDAL = ROOT / "formal/fstar/ocaml-output/factoidal"
PIPELINE = ROOT / "tools/corpus_pipeline.py"
DEFAULT_PYCOTTAS = ROOT / "_tmp.junk/pycottas-venv/bin/python"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Benchmark factoidal backends on the same query")
    parser.add_argument("--input", required=True, help="Input N-Quads file")
    parser.add_argument("--query", required=True, help="SPARQL query file")
    parser.add_argument("--repetitions", type=int, default=5)
    parser.add_argument("--warmup", type=int, default=1)
    parser.add_argument("--dataset-name", default="bench-cottas")
    parser.add_argument("--chunk-name", default="bench-cottas")
    parser.add_argument("--keep-workdir", action="store_true")
    parser.add_argument("--disk", action="store_true", help="Use disk-backed DuckDB for pycottas conversion")
    return parser


def run_checked(cmd: list[str], env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, check=True, text=True, capture_output=True, env=env)


def time_command(cmd: list[str], env: dict[str, str], warmup: int, repetitions: int) -> list[float]:
    for _ in range(warmup):
        run_checked(cmd, env)

    timings: list[float] = []
    for _ in range(repetitions):
        started = time.perf_counter()
        run_checked(cmd, env)
        timings.append((time.perf_counter() - started) * 1000.0)
    return timings


def summarise(name: str, timings: list[float]) -> str:
    return (
        f"{name}: runs={len(timings)} "
        f"best_ms={min(timings):.2f} "
        f"median_ms={statistics.median(timings):.2f} "
        f"mean_ms={statistics.mean(timings):.2f}"
    )


def main() -> int:
    args = build_parser().parse_args()
    env = dict(os.environ)
    pycottas_python = env.get("PYCOTTAS_PYTHON", str(DEFAULT_PYCOTTAS))
    env.setdefault("PYCOTTAS_PYTHON", pycottas_python)
    env.setdefault("FACTOIDAL_COTTAS_BRIDGE", str(ROOT / "tools/cottas_bridge.py"))

    workdir_obj = tempfile.TemporaryDirectory(prefix="factoidal-backend-bench-")
    workdir = Path(workdir_obj.name)
    corpus_root = workdir / "CorpusCOTTA"
    artifact_file = corpus_root / args.dataset_name / "v1" / "data.cottas"

    materialize_cmd = [
        pycottas_python,
        str(PIPELINE),
        "materialize-nq-cottas-corpus",
        "--input",
        args.input,
        "--corpus-root",
        str(corpus_root),
        "--dataset-name",
        args.dataset_name,
        "--chunk-name",
        args.chunk_name,
    ]
    if args.disk:
        materialize_cmd.append("--disk")
    run_checked(materialize_cmd, env)

    nq_cmd = [str(FACTOIDAL), "--data", args.input, "--query", args.query]
    cottas_cmd = [str(FACTOIDAL), "--data-cottas", str(artifact_file), "--query", args.query]

    nq_timings = time_command(nq_cmd, env, args.warmup, args.repetitions)
    cottas_timings = time_command(cottas_cmd, env, args.warmup, args.repetitions)

    print(summarise("nq", nq_timings))
    print(summarise("cottas", cottas_timings))

    if args.keep_workdir:
        print(f"workdir={workdir}")
    else:
        workdir_obj.cleanup()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

