#!/usr/bin/env python3
"""Generate a deeply-nested XML document: <a><a>...<a/>...</a></a>.

Used by task #49 (XML generality sanity check) to probe
Parser.XML.fst's parse_xml_element / parse_children recursion for
native-stack behavior at large nesting depths. Not part of the build;
investigation-only.

Usage: gen_deep_nesting.py <depth> <output-path>
"""
import sys

def main():
    depth = int(sys.argv[1])
    out_path = sys.argv[2]
    with open(out_path, "w") as f:
        f.write('<?xml version="1.0"?>\n')
        for _ in range(depth):
            f.write("<a>")
        f.write("leaf")
        for _ in range(depth):
            f.write("</a>")

if __name__ == "__main__":
    main()
