# xml_probe — ad-hoc XML generality driver (task #49)

Investigation-only tool. Not wired into `build-ocaml.sh`; not a
`bin/<consumer>` per iron rule #11 (it is a throwaway diagnostic, not a
shipped consumer). I/O glue only — no XML logic here — links the
extracted `Parser_XML` / `XML_Wellformedness` / `XML_Namespaces`
modules directly, same scratch-compile pattern as
`bin/xml-runner/README.md`.

## Build

```bash
eval $(opam env --switch=fstar)
SCRATCH=$(mktemp -d)
cp formal/fstar/ocaml-output/Parser_FastString_Spec.ml \
   formal/fstar/ocaml-output/Parser_FastString_CharBoundary.ml \
   formal/fstar/ocaml-output/Parser_FastString.ml \
   formal/fstar/ocaml-output/Parser_Combinators.ml \
   formal/fstar/ocaml-output/Parser_XML.ml \
   formal/fstar/ocaml-output/XML_Wellformedness.ml \
   formal/fstar/ocaml-output/XML_Namespaces.ml \
   tests/xml-generality/driver/xml_probe.ml "$SCRATCH"/
cd "$SCRATCH"
ocamlfind ocamlopt -package fstar.lib,zarith,unix -linkpkg -w -8-14-26-20 \
  Parser_FastString_Spec.ml Parser_FastString_CharBoundary.ml \
  Parser_FastString.ml Parser_Combinators.ml Parser_XML.ml \
  XML_Wellformedness.ml XML_Namespaces.ml xml_probe.ml -o xml_probe
```

## Run

```bash
xml_probe <file.xml>            # parse, report PARSED/REJECTED, run
                                 # the namespace-wellformedness check
xml_probe <file.xml> -bench     # + parse_time_s and VmHWM (peak RSS)
xml_probe <file.xml> -dump      # + every attribute value and text run,
                                 # both as OCaml %S and hex, so
                                 # whitespace-normalization and
                                 # line-ending questions are answerable
                                 # by inspection instead of guessing
```

## Companion generators

- `../gen_deep_nesting.py <depth> <out.xml>` — `<a><a>...leaf...</a></a>`
  at a given nesting depth, for native-stack-behavior probing.
- `../gen_large_doc.py <target-bytes> <out.xml>` — a flat, wide,
  RDF/XML-shaped document (many sibling `rdf:Description` records), for
  DOM-materialization time/memory probing.

See `docs/designissues/2026-08-10-xml-generality-findings.md` for what
these found.
