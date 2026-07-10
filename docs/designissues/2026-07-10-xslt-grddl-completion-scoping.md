# 2026-07-10 — XSLT 1.0 + GRDDL completion scoping

Status: scoping from the measured fail lists (committed
`xslt_results.log` 69 pass, 19 fail of 88; `grddl_results.log`
9 pass, 8 fail, 51 skip of 68). Not from memory — every cluster below
names its tests.

## XSLT 1.0: the 19 fails cluster into six features

| Cluster | Tests | What is actually missing | Size |
|---|---|---|---|
| Namespace-node model | namespace-1701/4101/4501, node-1601, copy-0601, match-045, conflict-resolution-1301 | The big rock (~7 of 19): the `namespace::` axis (node-1601 emits an empty NSlist), namespace-node copying, literal-result-element default-namespace fixup (namespace-4501: LRE must carry `xmlns="http://literalURI"` and children must UN-declare), namespace-aware match patterns for unprefixed names (match-045 re-serializes xhtml-ns elements with prefixes instead of matching/outputting per stylesheet intent), and ns-declaration serialization order (conflict-resolution-1301 is only attribute-order divergence — may need canonical ns ordering in the serializer, not new semantics) | **M** — one coherent slice: represent namespace nodes in the data model, expose the axis, fix LRE/copy fixup, canonicalize decl order |
| Axes document-order details | axes-047/090/184 | Proximity/document-order in `preceding`/`following` composites — outputs differ in a few positions (axes-090 drops "near-north" for AD; axes-184 misplaces "far-north") — ordering/dedup of multi-step axis results | **S-M** — likely one ordering bug in the axis evaluator |
| Boolean→string in AVTs | boolean-026/027 | `value="{true()}"` renders "" instead of "true" — the XPath boolean-to-string conversion is dropped somewhere in the AVT path | **S** — near-trivial |
| PI construction | construct-node-026 | `xsl:processing-instruction` result nodes not constructed (expected `<stylesheet>href=...` content absent) | **S** |
| Comment/whitespace copy | copy-2601 | Top-level comment (`<!-- Leave line-breaks as-is -->`) dropped when copying | **S** |
| node()/attribute + id() edges | node-1102, id-016 | Attribute node handling in generic node() iteration (missing "A:att"); id() pattern edge | **S** |

Estimate to 88/88: **one M agent run** (namespace-node model is the
majority of the work; the rest are S bugs that fall out per-cluster).
Highest-leverage repo-wide: the namespace-node model also unblocks
GRDDL below and hardens XPath for Schematron/XForms consumers.

## GRDDL: the 8 fails + 51 skips decompose into three tracks

**Track 1 — XSLT-fidelity-gated fails (5 of 8):** `hl7-to-owl`,
`projectsSpreadsheet` (grokSheet.xsl, the Gnumeric transform),
`title_author`, `rdfa1` (the RDFa-1.0-via-XSLT monster stylesheet),
and likely part of `noxinclude`. These run real-world stylesheets that
exercise exactly the namespace-node/axis features above. **Do XSLT
first, then re-measure — expect several to flip without GRDDL-side
work.**

**Track 2 — GRDDL engine semantics (3 of 8 + 2 stage-2 skips):**
- `xhtmlWithMoreThanOneGrddlTransformation` /
  `xhtmlWithMoreThanOneProfile`: multiple transforms/profiles on one
  document — run each transform, MERGE the result graphs (F\* engine
  logic, small).
- `xinclude` / `noxinclude`: decide XInclude posture (the pair tests
  that a GRDDL processor does/doesn't XInclude before transforming —
  read both expectations; likely we need XInclude *not* applied plus
  correct base handling, cheaper than implementing XInclude).
- The 2 `skip-stage2-ns-or-profile-document` tests: fetch the profile/
  namespace document, look for `grddl:profileTransformation` /
  `grddl:namespaceTransformation`, apply — needs the Track-3 fetch
  hook. Size: **S-M** total.

**Track 3 — the 49 `skip-network` (NetworkedTest):** these fetch
documents/transforms from live W3C URLs. Completion = vendor the
referenced resources (they are stable W3C test fixtures; mirror them
under `third_party/testing/grddl-network/` with PROVENANCE) + a
document-loader hook in the runner resolving those URLs to vendored
files — the same shape as `jsonld_load_document`. No engine changes;
scoring flips from skip to measured. Some fixtures are HTML-tag-soup
(Stage 3) — if any networked test needs non-well-formed HTML parsing,
that subset stays honestly failed/skipped with per-ID reasons until a
tag-soup decision (out of scope here; XML parser handles XHTML).
Size: **M**, mostly vendoring diligence.

## Recommended sequencing

1. **XSLT completion agent** (M): the six clusters above; floors =
   current 69/88 fail-set diff, GRDDL 9/8/51, Schematron, XForms unit
   suites (all consume XPath).
2. **GRDDL Tracks 2+3 agent** (M): after XSLT lands; re-measure the 8
   fails first (Track 1 may have flipped), then multi-transform merge,
   XInclude posture, fetch hook + vendored network fixtures, stage-2
   profile/namespace transformation.
3. Ledger + dashboard rows update per landing (obsolescence sweep both
   times — the GRDDL family prose currently says "Stage 2 = ... need a
   fetch hook" and the hub post 26 prose will date).

Combined estimate: two M agent runs to take XSLT to 88/88 (or
enumerated residue) and GRDDL from 9/8/51 to a mostly-measured suite
with only genuinely-unrunnable residue.
