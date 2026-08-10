#!/usr/bin/env python3
"""Generate a large, flat, RDF/XML-shaped XML document (many sibling
elements, not deep nesting) to probe Parser.XML.fst's DOM-materialization
cost: parse time and peak RSS on a big document. Not part of the build;
investigation-only, task #49.

Usage: gen_large_doc.py <target-bytes> <output-path>
"""
import sys

RECORD = (
    '  <rdf:Description rdf:about="http://example.org/item/{i}">\n'
    '    <dc:title>Item number {i}</dc:title>\n'
    '    <dc:creator>Generator Script</dc:creator>\n'
    '    <dc:description>Synthetic record {i} for large-document parse/memory probing.</dc:description>\n'
    '  </rdf:Description>\n'
)

HEADER = (
    '<?xml version="1.0"?>\n'
    '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"\n'
    '         xmlns:dc="http://purl.org/dc/elements/1.1/">\n'
)
FOOTER = '</rdf:RDF>\n'

def main():
    target_bytes = int(sys.argv[1])
    out_path = sys.argv[2]
    with open(out_path, "w") as f:
        f.write(HEADER)
        written = len(HEADER) + len(FOOTER)
        i = 0
        while written < target_bytes:
            rec = RECORD.format(i=i)
            f.write(rec)
            written += len(rec)
            i += 1
        f.write(FOOTER)
    print(f"wrote {out_path}: {written} bytes, {i} records")

if __name__ == "__main__":
    main()
