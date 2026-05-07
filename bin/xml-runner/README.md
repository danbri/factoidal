# bin/xml-runner — W3C XML Test Suite harness (scaffold)

Phase 0 placeholder for the XML-in-F\* stretch goal
([#185](https://github.com/danbri/factoidal/issues/185)). The runner
itself lands in Phase 1; this directory exists now so the design doc
can reference a concrete location and so that follow-up PRs have a
home for the runner ML and its support files.

See
[`docs/designissues/2026-05-07-xml-fstar-phase0-audit.md`](../../docs/designissues/2026-05-07-xml-fstar-phase0-audit.md)
for the audit, the extend-vs-build-alongside decision, the
EverParse-fit assessment, and the test-corpus vendoring plan.

## What lands here in Phase 1

```
bin/xml-runner/
├── README.md            -- this file
├── .placeholder         -- Phase 0 marker (delete in Phase 1)
├── xml_runner.ml        -- (Phase 1) entry point; reads the W3C
│                           manifest, dispatches each test through
│                           the F*-extracted Parser.XMLDoc, prints
│                           pass / fail / skip / total per subsuite
├── exclusions.txt       -- (Phase 1) test IDs deliberately skipped
│                           with a one-line reason per ID
└── dune                 -- (Phase 1) ocamlfind / dune build glue
```

Per CLAUDE.md rule #11 (consumer relocation), `xml-runner` is a
consumer, not part of the verified library. Hand-written OCaml here
is allowed; the verified work happens in `formal/fstar/XML.Core.fst`,
`formal/fstar/XML.Namespaces.fst`, and `formal/fstar/Parser.XMLDoc.fst`
(all Phase 1 deliverables).

## Output format

Per anti-pattern #25 (never write cryptic score strings —
"972/59" without labels is banned), the runner output is always
`pass / fail / skip / total` per subsuite:

```
=== W3C XML Test Suite ===
Test base: third_party/testing/xml/

Suite Results:
  xmltest/valid                   pass:N1   fail:F1   skip:S1   (out of T1)
  xmltest/not-wf                  pass:N2   fail:F2   skip:S2   (out of T2)
  ...
TOTAL: N pass, F fail, S skip, U unsupported (out of T)
```

Initially expect a high `fail` count — that is the **honest baseline**
the audit predicts (DTD-using tests, namespace-using tests, XML 1.1
tests will all fail or be skipped). Phases 2–3 reduce `fail`; the
runner reports honestly the whole way.

## Test corpus

Not vendored in this PR. Phase 1 lands the W3C XML Test Suite under
`third_party/testing/xml/` per the plan in the audit doc. Until then
the runner has no inputs; this directory only documents the shape.

## CLI sketch (Phase 1)

```
xml-runner --suite=all              # run everything
xml-runner --suite=xmltest          # run one subsuite
xml-runner --list                   # enumerate subsuites
xml-runner --verbose                # log every fail to stderr
xml-runner --json                   # machine-readable for dashboard
```

## Build (Phase 1)

```bash
eval $(opam env --switch=fstar)
cd formal/fstar
./build-ocaml.sh extract   # produces ocaml-output/Parser_XMLDoc.ml etc.
./build-ocaml.sh compile   # builds bin/<platform>/factoidal AND
                           # bin/<platform>/xml_runner once wired
```

## Phase status

- Phase 0 (this PR): scaffold only — README + `.placeholder`.
- Phase 1: runner ML + manifest reader + exclusions list.
- Phase 2: subsuites pass with namespace-aware parser.
- Phase 3: `Parser.RDFXML` migrates onto the new core; the existing
  in-tree consumer becomes the integration test.
- Phase 4: RSS / Atom / Sitemap XML / RIF-XML consumers join.
- Phase 5: dashboard panel surfaces the score honestly.
