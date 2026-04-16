#!/usr/bin/env python3

import argparse
import json
import hashlib
from pathlib import Path


def bloom_positions(value: str, m: int, k: int) -> list[int]:
    digest = hashlib.sha256(value.encode("utf-8")).digest()
    h1 = int.from_bytes(digest[:16], "big")
    h2 = int.from_bytes(digest[16:], "big") or 1
    return [((h1 + i * h2) % m) for i in range(k)]


def test_bit(buf: bytes, bit_index: int) -> bool:
    byte_index = bit_index // 8
    mask = 1 << (bit_index % 8)
    return (buf[byte_index] & mask) != 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Check a predicate Bloom sidecar for possible membership.")
    parser.add_argument("meta", help="Path to graph.bloom.pred.json")
    parser.add_argument("predicate", help="Predicate IRI to test")
    args = parser.parse_args()

    meta_path = Path(args.meta)
    meta = json.loads(meta_path.read_text(encoding="utf-8"))
    bin_path = meta_path.with_name(meta["binary"])
    buf = bin_path.read_bytes()
    m = int(meta["bit_count"])
    k = int(meta["hash_count"])
    positions = bloom_positions(args.predicate, m, k)
    ok = all(test_bit(buf, pos) for pos in positions)
    print(f"meta={meta_path}")
    print(f"binary={bin_path}")
    print(f"predicate={args.predicate}")
    print(f"result={'possibly-present' if ok else 'definitely-absent'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
