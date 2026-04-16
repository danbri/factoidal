#!/usr/bin/env python3

import argparse
import hashlib
import json
import math
from pathlib import Path


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def bloom_params(item_count: int, bits_per_item: int, hash_count: int) -> tuple[int, int]:
    m = max(1024, item_count * bits_per_item)
    k = max(1, hash_count)
    return m, k


def bloom_positions(value: str, m: int, k: int) -> list[int]:
    digest = hashlib.sha256(value.encode("utf-8")).digest()
    h1 = int.from_bytes(digest[:16], "big")
    h2 = int.from_bytes(digest[16:], "big") or 1
    return [((h1 + i * h2) % m) for i in range(k)]


def set_bit(buf: bytearray, bit_index: int) -> None:
    byte_index = bit_index // 8
    mask = 1 << (bit_index % 8)
    buf[byte_index] |= mask


def scan_predicates_from_nt(path: Path) -> set[str]:
    preds: set[str] = set()
    with path.open("r", encoding="utf-8") as src:
        for line_no, line in enumerate(src, start=1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            try:
                first = line.index(" ")
                second_start = first + 1
                second_end = line.index(" ", second_start)
                pred = line[second_start:second_end]
                if pred.startswith("<") and pred.endswith(">"):
                    preds.add(pred[1:-1])
                else:
                    raise ValueError(f"predicate not in IRI form: {pred}")
            except Exception as exc:
                raise RuntimeError(f"{path}:{line_no}: {exc}") from exc
    return preds


def write_predicate_bloom(graph_dir: Path, nt_path: Path, bits_per_item: int, hash_count: int, overwrite: bool) -> None:
    bloom_bin = graph_dir / "graph.bloom.pred.bin"
    bloom_json = graph_dir / "graph.bloom.pred.json"
    if not overwrite and bloom_bin.exists() and bloom_json.exists():
      return

    preds = scan_predicates_from_nt(nt_path)
    m, k = bloom_params(len(preds), bits_per_item, hash_count)
    buf = bytearray(math.ceil(m / 8))
    for pred in preds:
        for pos in bloom_positions(pred, m, k):
            set_bit(buf, pos)

    ensure_parent(bloom_bin)
    bloom_bin.write_bytes(bytes(buf))
    bloom_json.write_text(
        json.dumps(
            {
                "kind": "predicate-bloom-v1",
                "source": nt_path.name,
                "predicate_count": len(preds),
                "bit_count": m,
                "hash_count": k,
                "bits_per_item": bits_per_item,
                "binary": bloom_bin.name,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


def write_predicate_bloom_fixed(
    graph_dir: Path,
    nt_path: Path,
    fixed_bit_count: int,
    hash_count: int,
    overwrite: bool,
) -> tuple[int, int]:
    bloom_bin = graph_dir / "graph.bloom.pred.bin"
    bloom_json = graph_dir / "graph.bloom.pred.json"
    if not overwrite and bloom_bin.exists() and bloom_json.exists():
        meta = json.loads(bloom_json.read_text(encoding="utf-8"))
        return int(meta["predicate_count"]), int(meta["bit_count"])

    preds = scan_predicates_from_nt(nt_path)
    m = max(1024, fixed_bit_count)
    k = max(1, hash_count)
    buf = bytearray(math.ceil(m / 8))
    for pred in preds:
        for pos in bloom_positions(pred, m, k):
            set_bit(buf, pos)

    bloom_bin.write_bytes(bytes(buf))
    bloom_json.write_text(
        json.dumps(
            {
                "kind": "predicate-bloom-v1",
                "source": nt_path.name,
                "predicate_count": len(preds),
                "bit_count": m,
                "hash_count": k,
                "bits_per_item": None,
                "fixed_bit_count": m,
                "binary": bloom_bin.name,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    return len(preds), m


def process_corpus(
    root: Path,
    bits_per_item: int,
    hash_count: int,
    overwrite: bool,
    fixed_bit_count: int | None,
) -> tuple[int, int]:
    graph_count = 0
    predicate_total = 0
    for nt_path in root.glob("*/v1/data.nt"):
        graph_dir = nt_path.parent
        if fixed_bit_count is None:
            preds = scan_predicates_from_nt(nt_path)
            predicate_total += len(preds)
            m, k = bloom_params(len(preds), bits_per_item, hash_count)
            buf = bytearray(math.ceil(m / 8))
            for pred in preds:
                for pos in bloom_positions(pred, m, k):
                    set_bit(buf, pos)
            bloom_bin = graph_dir / "graph.bloom.pred.bin"
            bloom_json = graph_dir / "graph.bloom.pred.json"
            if overwrite or not (bloom_bin.exists() and bloom_json.exists()):
                bloom_bin.write_bytes(bytes(buf))
                bloom_json.write_text(
                    json.dumps(
                        {
                            "kind": "predicate-bloom-v1",
                            "source": nt_path.name,
                            "predicate_count": len(preds),
                            "bit_count": m,
                            "hash_count": k,
                            "bits_per_item": bits_per_item,
                            "fixed_bit_count": None,
                            "binary": bloom_bin.name,
                        },
                        indent=2,
                        sort_keys=True,
                    )
                    + "\n",
                    encoding="utf-8",
                )
        else:
            pred_count, _ = write_predicate_bloom_fixed(
                graph_dir,
                nt_path,
                fixed_bit_count,
                hash_count,
                overwrite,
            )
            predicate_total += pred_count
        graph_count += 1
    return graph_count, predicate_total


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate predicate Bloom sidecars for graph folders.")
    parser.add_argument("root", help="Corpus root or graph root to scan")
    parser.add_argument("--bits-per-item", type=int, default=16)
    parser.add_argument("--hash-count", type=int, default=7)
    parser.add_argument("--fixed-bit-count", type=int, help="Use the same Bloom bit count for every graph so sidecars can be OR-rolled later")
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()

    root = Path(args.root)
    graph_count, predicate_total = process_corpus(
        root,
        args.bits_per_item,
        args.hash_count,
        args.overwrite,
        args.fixed_bit_count,
    )
    print(f"root={root}")
    print(f"graphs={graph_count}")
    print(f"predicate_total={predicate_total}")
    if args.fixed_bit_count is not None:
        print(f"fixed_bit_count={args.fixed_bit_count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
