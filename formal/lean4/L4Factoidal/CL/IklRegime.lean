/-
L4Factoidal.CL.IklRegime — the `x-ikl-*` entailment-regime family.

Owner ruling (2026-08-25, recorded verbatim in
https://github.com/danbri/factoidal/issues/581): "X-ikl regimes - try
to postpone fixing of exact regime but allow any 'x-ikl-blah' strings
to trigger ikl and perhaps later invoke subsets".

So this module fixes the FAMILY, not the semantics:

* The regime-string matcher accepts `x-ikl` and every string of the
  form `x-ikl-<suffix>` as ONE recognized family. An unknown suffix is
  NOT an error. Matching is exact and case-sensitive on the `x-ikl`
  prefix, the convention `RDFS/RegimeDispatch.lean` uses for
  `x-rdfscore` / `x-rdfsplus`. `x-iklx` and `ikl` are NOT members.
* The suffix is parsed off and carried in the `IklRegime` value, so a
  later change can bind named subsets (`x-ikl-flat`, `x-ikl-finite`,
  ...) inside `IklRegime.extendDataset` without touching the plumbing
  that recognizes the family.
* Every suffix currently routes to the SAME handler with the SAME
  PROVISIONAL default behavior, documented at `extendDataset`.

## The provisional default (all suffixes) — see issue 581

BGP matching over the dataset extended by the ASSERTED-proposition
rule: the content of every proposition the default graph ASSERTS is
made reachable from the default graph. Concretely, `extendDataset`
merges into the default graph every named graph

1. whose graph name is an IRI starting with `urn:cl:that:` (the
   proposition-IRI convention `CL/ToRdf.lean` emits under the
   `urn:cl:` base — `propIri` produces `<base ++ "that:sha256:" ++
   hex64>`, the content address of the alpha-normalized canonical
   CLIF; issue 589), and
2. whose name is the OBJECT of a default-graph triple with predicate
   `urn:cl:def:asserts` — `CL/ToRdf.lean`'s assertion decoration
   (any asserting subject).

NARROWED 2026-08-25 with the graph-decoration translation
(https://github.com/danbri/factoidal/issues/581): trigger 2 used to be
"object of ANY default-graph triple", so a mere LINK decoration
(`believes`, `ist`, `says`, ...) merged its proposition's content —
but a predication about a proposition does not assert it. Under the
current rule only the `urn:cl:def:asserts` decoration merges; link
decorations leave their graphs `GRAPH`-visible and nothing more.

Nothing else: one pass, no recursion into propositions asserted only
inside other propositions, no quantifiers, no negation. Named subsets
and their exact semantics are DEFERRED, tracked in issue 581; do not
build on the details of this default.

## Encoding commitment (review disposition, owner-relayed 2026-08-25)

RDF semantics does not identify a graph name with the graph it names:
RDF 1.1 datasets leave the relation between a graph name and its
graph uninterpreted. Factoidal's `x-ikl-*` regime family additionally
interprets the proposition IRI BOTH as the proposition's identifier
(the term link decorations and the `urn:cl:def:asserts` decoration
point at) AND, syntactically, as the name of the named graph holding
the proposition's RDF projection (its translatable atoms plus its
sentence record, `CL/ToRdf.lean`). That double reading is a
deliberate extra semantic commitment of this regime, not an RDF
entailment: nothing in RDF semantics licenses treating membership in
the graph named by an IRI as content of the proposition that IRI
identifies.

The commitment is now stated in the model theory as
`Unified.IklAssertionCommitment` (`Unified/ClBridge.lean`,
https://github.com/danbri/factoidal/issues/609 item 3), over the
`urn:cl:def:names` and `urn:cl:def:asserts` vocabulary alone. Under it
plus `CL.IklRespectsThat`, the unified layer's dataset embedding
entails the whole default graph `extendDataset` computes, on datasets
with no blank nodes. WITHOUT it the two disagree, and the divergence
is machine-checked: `commitment_not_derivable` shows the condition is
not a consequence of IKL coherence.
-/

import L4Factoidal.CL.ToRdf

namespace L4Factoidal.CL

/-! ## The family matcher -/

/-- A recognized member of the `x-ikl-*` regime family, carrying the
suffix (`""` for bare `x-ikl`, `"flat"` for `x-ikl-flat`, ...). The
suffix is carried so later work can bind named subsets without
changing the recognition or the plumbing (issue 581). -/
structure IklRegime where
  suffix : String
  deriving DecidableEq, Repr

/-- The family name. A regime string is in the family when it equals
this or starts with this plus `-`. -/
def iklFamilyName : String := "x-ikl"

/-- Parse a regime string into the family: `x-ikl` → suffix `""`,
`x-ikl-<s>` → suffix `<s>` (any `<s>`, unknown suffixes included —
per the owner ruling in issue 581 they are recognized, not errors).
Anything else — `x-iklx`, `ikl`, other regimes — is `none`.
Case-sensitive exact match on the family name, like the
`x-rdfscore` / `x-rdfsplus` matchers. -/
def IklRegime.parse? (s : String) : Option IklRegime :=
  if s == iklFamilyName then some ⟨""⟩
  else if s.startsWith (iklFamilyName ++ "-") then
    some ⟨(s.drop (iklFamilyName.length + 1)).toString⟩
  else none

/-! ## The one handler (provisional default semantics) -/

/-- The proposition-IRI prefix the default behavior recognizes:
`CL/ToRdf.lean`'s `propIri` under the `urn:cl:` base. PROVISIONAL —
a translation under a different base is not seen (issue 581). -/
def propositionGraphPrefix : String := "urn:cl:that:"

/-- Is this graph name a proposition IRI (by the provisional
convention)? A blank-node graph name never is. -/
def isPropositionGraphName : RDF.Subject → Bool
  | .iri i  => i.val.startsWith propositionGraphPrefix
  | .bnode _ => false

/-- Does the default graph ASSERT the proposition named `name` — is
`name` the object of a default-graph triple whose predicate is
`urn:cl:def:asserts` (`CL/ToRdf.lean`'s assertion decoration; any
asserting subject)? A link decoration (`believes`, `ist`, ...) does
NOT satisfy this — see the module header's narrowing note (issue
581). -/
def assertsDecorated (dflt : RDF.Graph) : RDF.Subject → Bool
  | .iri i   => dflt.any (fun t => t.p == clDefAssertsIri && t.o == RDF.Term.iri i)
  | .bnode _ => false

/-- The ONE `x-ikl-*` handler. PROVISIONAL DEFAULT for every suffix
(the suffix is deliberately not yet inspected — named subsets are
deferred, https://github.com/danbri/factoidal/issues/581): the
default graph is extended with the content of every ASSERTED
proposition — every named graph whose name is a proposition IRI
(`propositionGraphPrefix`) occurring as the object of a default-graph
`urn:cl:def:asserts` decoration. One pass over the ORIGINAL default
graph: a proposition asserted only inside another proposition's
content is not merged. Named graphs are left in place, so `GRAPH`
patterns still see them. -/
def IklRegime.extendDataset (_r : IklRegime) (ds : RDF.Dataset) : RDF.Dataset :=
  { ds with
    default := ds.named.foldl
      (fun acc ng =>
        if isPropositionGraphName ng.name && assertsDecorated ds.default ng.name
        then RDF.Graph.union acc ng.graph
        else acc)
      ds.default }

/-! ## Build-time checks

### (a) Family acceptance, suffix carried -/

#guard IklRegime.parse? "x-ikl" == some ⟨""⟩
#guard IklRegime.parse? "x-ikl-flat" == some ⟨"flat"⟩
#guard IklRegime.parse? "x-ikl-anything-at-all" == some ⟨"anything-at-all"⟩

/-! ### (b) Near-misses are NOT members -/

#guard IklRegime.parse? "x-iklx" == none
#guard IklRegime.parse? "ikl" == none
#guard IklRegime.parse? "X-IKL" == none      -- exact case, like x-rdfscore
#guard IklRegime.parse? "x-rdfscore" == none
#guard IklRegime.parse? "" == none

/-! ### (c) The default behavior, over the `ToRdf` assertion example

`((that (Dead OBL)))` asserts the proposition: the translation
decorates its named graph with `urn:cl:def:asserts`, and the handler
makes the content triple visible in the default graph. -/

private def exBase : IriBase := ⟨"urn:cl:", rfl⟩

/-- A CLIF text's dataset, via the real parser and translator
(`Dataset.empty` only on a parse/translate failure, which the guards
below would then catch as missing triples). -/
private def dsOf (text : String) : RDF.Dataset :=
  match parseClifText text with
  | .error _ => RDF.Dataset.empty
  | .ok ss =>
      match toRdfDataset "urn:cl:" ss with
      | .error _ => RDF.Dataset.empty
      | .ok r => r.ds

/-- The asserted example. -/
private def exDs : RDF.Dataset := dsOf "((that (Dead OBL)))"

/-- The content triple `<urn:cl:OBL> rdf:type <urn:cl:Dead>`. -/
private def exContent : RDF.Triple :=
  { s := .iri (nameIri exBase "OBL"), p := rdfTypeIri,
    o := .iri (nameIri exBase "Dead") }

private def exRegime : IklRegime := ⟨"flat"⟩

private def exProp : RDF.WfIri :=
  propIri exBase (.atom (.name "Dead") [.term (.name "OBL")])

-- The graph name `propIri` emits (`urn:cl:that:sha256:<hex64>`) is
-- inside the prefix the handler recognizes.
#guard isPropositionGraphName (.iri exProp) == true

-- Before: the content triple lives only in the named graph.
#guard exDs.default.mem exContent == false
-- After: the handler makes it default-graph (BGP-) matchable...
#guard (exRegime.extendDataset exDs).default.mem exContent == true
-- ...and the named graph itself is still there for GRAPH patterns.
#guard ((exRegime.extendDataset exDs).lookupNamed (.iri exProp)).isSome

/-! ### (d) What the default does NOT do -/

-- The narrowing (issue 581): a LINK decoration is not an assertion.
-- `(ist c (that (Dead OBL)))` decorates the same proposition graph
-- with an `ist` link only, so its content is NOT merged.
#guard (exRegime.extendDataset (dsOf "(ist c (that (Dead OBL)))")).default.mem
        exContent == false

/-- A dummy digest in the `that:sha256:<hex64>` shape, for the
unasserted-graph check below. -/
private def exDummySuffix : String :=
  "that:sha256:0000000000000000000000000000000000000000000000000000000000000000"

/-- A proposition-named graph the default graph never asserts (no
decoration at all): its content must NOT be merged. -/
private def unassertedDs : RDF.Dataset :=
  { default := [],
    named := [{ name := .iri (exBase.mk' exDummySuffix), graph := [exContent] }] }

#guard (exRegime.extendDataset unassertedDs).default.mem exContent == false

/-- An asserts-decorated named graph OUTSIDE the proposition
convention: not merged either, even though the default graph carries
an `urn:cl:def:asserts` triple pointing at it. -/
private def nonPropDs : RDF.Dataset :=
  { default := [{ s := .iri clKbIri, p := clDefAssertsIri,
                  o := .iri (nameIri exBase "g") }],
    named := [{ name := .iri (nameIri exBase "g"), graph := [exContent] }] }

#guard (exRegime.extendDataset nonPropDs).default.mem exContent == false

end L4Factoidal.CL
