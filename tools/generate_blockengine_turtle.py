#!/usr/bin/env python3
"""Generate a deterministic default-graph Turtle workload for Lean SBM6 tests.

This intentionally complements—not replaces—the checked-in Wikidata KGX
corpora.  It gives the block engine controlled object selectivity and a shared
subject join shape without downloading an opaque external dump.
"""

import argparse
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, help="Turtle file to create")
    parser.add_argument("--subjects", type=int, default=4096,
                        help="number of deterministic subject records")
    parser.add_argument("--types", type=int, default=16,
                        help="number of repeated object type values")
    parser.add_argument("--parents", type=int, default=256,
                        help="number of repeated parent object values")
    args = parser.parse_args()
    if args.subjects < 1 or args.types < 1 or args.parents < 1:
        parser.error("subjects, types, and parents must all be positive")

    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", encoding="utf-8") as handle:
        handle.write("@prefix ex: <urn:factoidal:synthetic:> .\n\n")
        for number in range(args.subjects):
            handle.write(
                f"ex:s{number} ex:type ex:type{number % args.types} ;\n"
                f"  ex:parent ex:parent{number % args.parents} ;\n"
                f"  ex:label \"record {number}\"@en .\n"
            )
    print(f"{output} triples={args.subjects * 3} subjects={args.subjects} "
          f"types={args.types} parents={args.parents}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
