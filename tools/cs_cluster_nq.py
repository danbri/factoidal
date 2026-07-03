#!/usr/bin/env python3
"""Characteristic-set row clustering for N-Quads (experiment E1).

Reads N-Quads from stdin or a file and emits the same quads to stdout
re-ordered by ``(CS(subject), subject, predicate, object, graph)``,
where ``CS(subject)`` is the characteristic set of the subject — the
sorted set of predicates that subject has anywhere in the input
(Neumann & Moerkotte, ICDE 2011) — hashed to a compact sort key.

Rationale: COTTAS v1 row order is producer-chosen and semantically
free (docs/cottas-format-v1.md §3), so re-ordering rows before the
Parquet write is a zero-reader-cost lever on compression and row-group
prune selectivity. See
docs/designissues/2026-07-03-shapes-canon-storage-strategies.md §1.3
and experiment E1 in §5.

Python stdlib only. Whole input is buffered in memory (two passes are
needed anyway: CS discovery, then sort).

Usage:
    cs_cluster_nq.py [--stats] [FILE]
    cat data.nq | cs_cluster_nq.py --stats > clustered.nq

--stats prints, to stderr: number of distinct characteristic sets,
a subjects-per-CS histogram summary (min/median/max), and input/output
quad counts (which must be equal).
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from statistics import median


class NQuadsSyntaxError(ValueError):
    pass


def _scan_iriref(line: str, i: int) -> int:
    """Return index one past the closing '>' of an IRIREF starting at i."""
    end = line.find(">", i + 1)
    if end == -1:
        raise NQuadsSyntaxError("unterminated IRIREF")
    return end + 1


def _scan_bnode(line: str, i: int) -> int:
    """Return index one past a blank node label starting at i ('_:...')."""
    j = i + 2
    n = len(line)
    while j < n and not line[j].isspace():
        j += 1
    return j


def _scan_literal(line: str, i: int) -> int:
    """Return index one past a literal starting at i (opening '\"'),
    including any @lang or ^^<datatype> suffix."""
    n = len(line)
    j = i + 1
    while j < n:
        c = line[j]
        if c == "\\":
            j += 2
            continue
        if c == '"':
            j += 1
            break
        j += 1
    else:
        raise NQuadsSyntaxError("unterminated literal")
    # Optional suffix.
    if j < n and line[j] == "@":
        while j < n and not line[j].isspace():
            j += 1
    elif line.startswith("^^", j):
        if j + 2 >= n or line[j + 2] != "<":
            raise NQuadsSyntaxError("malformed datatype suffix")
        j = _scan_iriref(line, j + 2)
    return j


def tokenize_quad(line: str) -> list[str]:
    """Split one N-Quads statement into its 3 or 4 term tokens.

    The trailing '.' must be present. Comments/blank lines are the
    caller's job. Tokens are returned as their raw N-Quads text.
    """
    tokens: list[str] = []
    i = 0
    n = len(line)
    while i < n:
        c = line[i]
        if c.isspace():
            i += 1
            continue
        if c == ".":
            rest = line[i + 1 :].strip()
            if rest:
                raise NQuadsSyntaxError(f"trailing content after '.': {rest!r}")
            if len(tokens) not in (3, 4):
                raise NQuadsSyntaxError(f"{len(tokens)} terms before '.'")
            return tokens
        if c == "<":
            j = _scan_iriref(line, i)
        elif c == '"':
            j = _scan_literal(line, i)
        elif line.startswith("_:", i):
            j = _scan_bnode(line, i)
        else:
            raise NQuadsSyntaxError(f"unexpected character {c!r} at column {i}")
        tokens.append(line[i:j])
        i = j
    raise NQuadsSyntaxError("statement not terminated by '.'")


def cs_key(predicates: frozenset[str]) -> str:
    """Compact, deterministic key for a characteristic set: SHA-256 of
    the newline-joined sorted predicate tokens, truncated to 16 hex
    chars (64 bits — collision-safe for any realistic CS count)."""
    payload = "\n".join(sorted(predicates)).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()[:16]


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        description="Re-order N-Quads by (characteristic-set-of-subject, s, p, o, g)."
    )
    ap.add_argument("file", nargs="?", default="-",
                    help="input N-Quads file (default: stdin)")
    ap.add_argument("--stats", action="store_true",
                    help="print CS statistics and quad counts to stderr")
    args = ap.parse_args(argv)

    if args.file == "-":
        src = sys.stdin
    else:
        src = open(args.file, "r", encoding="utf-8")

    # Pass 1: parse every statement, accumulate each subject's predicate set.
    rows: list[tuple[str, str, str, str, str]] = []  # (s, p, o, g, raw_line)
    subject_preds: dict[str, set[str]] = {}
    input_count = 0
    try:
        for line_no, raw in enumerate(src, start=1):
            stripped = raw.strip()
            if not stripped or stripped.startswith("#"):
                continue
            try:
                toks = tokenize_quad(stripped)
            except NQuadsSyntaxError as exc:
                print(f"{args.file}:{line_no}: {exc}", file=sys.stderr)
                return 1
            s, p, o = toks[0], toks[1], toks[2]
            g = toks[3] if len(toks) == 4 else ""
            rows.append((s, p, o, g, stripped))
            subject_preds.setdefault(s, set()).add(p)
            input_count += 1
    finally:
        if src is not sys.stdin:
            src.close()

    # CS key per subject (over the whole input, all graphs).
    subject_cs: dict[str, str] = {
        s: cs_key(frozenset(preds)) for s, preds in subject_preds.items()
    }

    # Pass 2: sort by (CS(s), s, p, o, g) and emit.
    rows.sort(key=lambda r: (subject_cs[r[0]], r[0], r[1], r[2], r[3]))

    out = sys.stdout
    output_count = 0
    for _, _, _, _, raw in rows:
        out.write(raw)
        out.write("\n")
        output_count += 1
    out.flush()

    if args.stats:
        cs_subject_counts: dict[str, int] = {}
        for s, key in subject_cs.items():
            cs_subject_counts[key] = cs_subject_counts.get(key, 0) + 1
        counts = sorted(cs_subject_counts.values())
        err = sys.stderr
        err.write(f"distinct characteristic sets: {len(counts)}\n")
        if counts:
            err.write(
                "subjects per CS: min {}, median {}, max {} "
                "(over {} subjects)\n".format(
                    counts[0], median(counts), counts[-1], len(subject_cs)
                )
            )
        err.write(f"input quads: {input_count}\n")
        err.write(f"output quads: {output_count}\n")
        if input_count != output_count:
            err.write("ERROR: input/output quad counts differ\n")
            return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
