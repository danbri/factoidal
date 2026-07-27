# JSON-LD Framing — why it is 6 pass, 86 fail (out of 92)

Date: 2026-07-27. Suite: `third_party/testing/json-ld-framing/tests`.
Runner: `bin/linux-x86_64/jsonld_frame_runner`. Algorithm:
`formal/fstar/JSONLD.Frame.fst` (290 lines, self-described "first cut").

## Failure buckets (measured)

- 68 — "framed JSON-LD differs from expected"
- 16 — "frame_document returned None on a positive test"
- 2 — "should reject but framed" (negative tests)

## Root causes

### 1. `@explicit=false` default is not implemented (the 68-bucket driver)

`frame_props` walks the FRAME's fields and outputs only the properties
the frame names. The framing spec default is `@explicit=false`, which
outputs EVERY property of a matched node; the frame's sub-frames only
shape the properties they mention, they do not restrict the set.

Example — test t0001 (Library framing). Frame names only `@type` +
`ex:contains`, yet the expected output carries `dcterms:title`,
`dcterms:contributor`, `dcterms:description` on the embedded nodes. Our
output drops them because they are not in the frame.

Fix shape: `frame_props` must iterate the NODE's own properties (in
order), look each up in the frame to pick a sub-frame (empty match-all
frame when absent), and drop unframed properties only when
`@explicit=true`.

### 2. No frame-expansion mode (blocks the fix for #1 and the 16-bucket)

`Parser.JSONLD.expand_document` (line 1410) has no `frameExpansion`
flag. Regular expansion:
- DROPS the framing keywords `@explicit`, `@default`, `@omitDefault`,
  `@requireAll`, `@embed` — so the algorithm cannot read them. This is
  why the fix for #1 cannot simply flip the default: the currently
  passing test "explicitly excludes unframed properties (@explicit:
  true)" needs `@explicit=true` to be READABLE, and it is not.
- DROPS empty-object property values `"prop": {}` (the match-present
  wildcard) and empty arrays `"prop": []` (match-absent) — losing frame
  structure. (Note: for `@explicit=false` output the wildcard's effect
  is recovered by the default "output all properties" path, so #1 does
  not strictly need the wildcard preserved; @default/@embed do.)

The 16 "returned None" are value-pattern frames ("matches wildcard
@value/@type/@language in value pattern") where the frame's `{}` value
objects vanish or expansion rejects the frame shape.

Fix shape: add `frame_expansion:bool` to `expand`/`expand_document`
(default false, so the 385/385 expand suite and every other caller are
untouched). In frame mode: preserve the five framing keywords, keep
empty `{}`/`[]`, and do not prune properties whose value expands empty.

### 3. Missing framing features (the tail)

Once #1 and #2 land, the remaining spec pieces:
- `@default` value insertion for missing framed properties.
- `@omitDefault`.
- `@requireAll` matching semantics (our `node_matches` already ANDs all
  constraints = requireAll=true; the default is requireAll=false = OR of
  the property constraints, with @type/@id still required when present).
- `@embed` variations (`@always`/`@never`/`@link`/`@once`).
- Blank-node `@id` pruning: framing removes an output node's `@id` when
  it is a blank-node identifier not referenced elsewhere. Several
  "differs" failures in the "Blank node" group are this.
- Value-object level matching inside a property frame (`@value`/@type/
  @language patterns) — ties to #2.

## Suggested order

1. `frame_expansion` in the expander (unblocks everything; guarded flag,
   zero risk to existing suites).
2. `@explicit` default in `JSONLD.Frame` (clears most of the 68).
3. `@requireAll` OR-matching + `@default`/@omitDefault.
4. Blank-node `@id` pruning + value-object matching.

Each step is independently measurable against the 92-test suite.
Parsers/algorithms stay in F\* (rules #1/#4); the runner is I/O only.
