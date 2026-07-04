# JSON-LD program: lessons applied up front

Cost-minimisation notes for the full-compliance JSON-LD program
(task: 101% conformant, incl. remote contexts), distilled from the
spec/test-suite structure, this codebase's precedents, and the
2026-04/07 perf war stories. Suite vendored 2026-07-04 at
`third_party/testing/json-ld` (w3c/json-ld-api, 837 toRdf test
files, `tests/toRdf-manifest.jsonld`).

## The two big scope cuts

1. **toRdf-only.** An RDF engine's conformance target is the
   `toRdf` manifest (expansion + deserialization to RDF). The
   `compact`, `flatten`, `frame`, and `html` manifests test
   JSON-to-JSON transformations we do not need for intake. This
   halves the algorithm surface: context processing + expansion +
   toRdf, nothing else.
2. **"Remote" contexts are suite-local files.** The test suite ships
   every remote document it references as a file, addressed by
   manifest-declared base IRIs. Conformance therefore needs a
   documentLoader ABSTRACTION (F\* `assume val load_document :
   iri -> option string` realised as fixture-file lookup), not live
   HTTP. Real network fetching is a production follow-up behind the
   same assume val (rule #11 ASSUME-IO; OCaml curl/socket realisation
   for native, a JS loader hook in the npm wrapper) — it never blocks
   the "101%" suite claim.

## Codebase precedents to imitate

- **Mirror the spec's algorithm numbering** the way `RDF.Canonical`
  mirrored RDFC-1.0 (which reached 62 pass of 86 quickly and
  debuggably): one F\* function per spec algorithm, spec section
  named in a `//` comment. The JSON-LD 1.1 API spec is already
  pseudocode; transliterate, don't re-derive.
- **Stratify small modules**: `Parser.JSON` (full RFC 8259 value
  parser, reusable), `JSONLD.Context` (context processing),
  `JSONLD.Expand`, `JSONLD.ToRdf`, `JSONLD.Loader` (assume-val
  boundary). Small modules keep the .checked cascade cheap
  (fast-verify-extract), keep verification honest (the
  `--admit_smt_queries` creep in SPARQL11.Parser started as one big
  module), and match the semantic-core-vs-pragmatics rule.
- **Keep mutual recursion inside one module** — cross-module forward
  refs were an extraction wound (#62 glue patch).
- **Reuse the existing codepoint/UTF-8 assume-vals**
  (`sparql_parser_stubs`: `utf8_of_codepoint_impl`) for \uXXXX
  escapes — no new glue.

## Perf war stories that apply directly

- **Output construction, not tokenization, is where O(N²) hides**
  (the Turtle lesson, twice): emit triples with
  `add_triple_unchecked`/prepend and dedup ONCE at the end; never
  membership-scan per emitted triple.
- **`nat` positions extract to Z.t bignums** — a per-char tax on
  string scanning. Phase 1 favours clarity; before optimising, wire a
  JSON fixture into the parse-perf bench (task #28) and measure. The
  byte-indexed `Parser.FastString` retrofit path exists if needed.
- **Never let a parse hang un-capped** (rule #17) and background
  anything slow (#19/#20).

## Runner + comparison

- The manifests are themselves compacted JSON-LD — until context
  processing lands, a small Python converter (tools/) flattens the
  manifest into the runner's plain list format (pure tooling, rule
  #15). Once `JSONLD.Context` exists, the runner can eat the
  manifest natively as a nice self-test.
- toRdf comparison is N-Quads isomorphism: reuse the runner's
  existing bnode comparison plus `canonicalize` for exact cases —
  and remember the runner's lenient-bnode caveat cuts both ways
  (test-suites skill).
- Per-backend rule applies here too: JSON-LD-loaded datasets join the
  cross-backend parity corpus once loadable.

## Phasing (task #26)

1. expanded-form → dataset (running) + full `Parser.JSON`.
2. Manifest converter + runner wiring; score the expanded-form subset
   of toRdf honestly (labelled: "expanded-form tests only").
3. `JSONLD.Context` + `JSONLD.Expand` (the big algorithm; spec §4).
4. Loader assume-val + fixture realisation → full toRdf runs.
5. Options coverage (ordered, rdfDirection, produceGeneralizedRdf) to
   close the tail; production HTTP loader; npm loader hook.
