# Blogic, RDF Surfaces, and graphs-with-substructure — literature review and design tie-ins

**Date:** 2026-07-04.
**Status:** design research only. No code changes, no format changes,
no commitments. §5 is a ranked list of experiments, per house style.
**Research question (project owner):** review the literature stemming
from Pat Hayes' 2009 "Blogic" ISWC keynote and the modern RDF
Surfaces line it seeded, plus the named-graphs / quoted-graphs /
graphs-as-first-class-citizens threads; tie in (a) refocusing the
system on **graphs over triples** — named graphs with *substructure*:
component graphs, possibly millions, each instantiating a
shape/pattern or mapping to SQL rows / XML documents — and (b) the
logic side of Blogic (surfaces as scoped negation/quantification, as
N3/EYE use it).

Source-marking convention (same as
[`2026-07-03-shapes-canon-storage-strategies.md`](2026-07-03-shapes-canon-storage-strategies.md)):
claims labelled **[web]** were checked against the cited source
during this session (the RDF Surfaces spec and test-suite repos were
cloned and read directly); **[web-listed]** means the work's
existence/venue was confirmed via search results but the full text
was not read; **[memory]** is from the author-model's training
knowledge and should be re-verified before anything load-bearing is
built on it. Claims about this repo cite files directly.

## 0. Where the tree is (grounding)

- **Dataset model.** `rdf_dataset = { ds_default : rdf_graph;
  ds_named : list named_graph }` with `named_graph = { ng_name : iri;
  ng_graph : rdf_graph }` and a linear `lookup_named_graph`
  ([`RDF.Graph.Executable.fst:146-162`](../../formal/fstar/RDF.Graph.Executable.fst)).
  Two properties matter below: graph names are IRIs only (RDF 1.1
  also permits blank-node graph names **[memory — RDF 1.1 Concepts
  §4]**), and the named-graph list is flat — no containment,
  composition, or nesting relations between graphs.
- **On-disk.** COTTAS-on-Parquet v1
  ([`docs/cottas-format-v1.md`](../cottas-format-v1.md)): four string
  columns `s,p,o,g`, `DEFAULT` sentinel for the default graph,
  122,880-row row groups, row order producer-chosen and semantically
  free (§3 of that doc). Quoted triples / RDF-star are explicitly out
  of scope for v1 (§10). Per-graph predicate Bloom sidecars exist
  ([`graph-bloom-sidecars.md`](graph-bloom-sidecars.md)).
- **Shapes as storage.** Characteristic-set row clustering was
  measured in E1
  ([`2026-07-03-e1-cs-clustering-results.md`](2026-07-03-e1-cs-clustering-results.md)):
  CS order compresses 39.5% better than arrival order and 3.3% better
  than SPOG order, and confines shape-specific predicates to a subset
  of row groups — the property the prune cascade needs. Verdict was
  "qualified yes", parliament re-run pending.
- **Canonicalization.**
  [`RDF.Canonical.fst`](../../formal/fstar/RDF.Canonical.fst)
  implements RDFC-1.0 HFDQ (62 pass, 23 fail, 1 skip of 86 rdf-canon
  tests); exposing it as `factoidal canonicalize` is standing
  priority #6, and E3 of the storage-strategies doc plans per-graph
  canonical-hash sidecars + Merkle roll-ups.
- **Negation machinery in SPARQL.** The engine passes the W3C
  negation suite 12 of 12 and exists suite 6 of 6
  ([`docs/claude-rules/current-state.md`](../claude-rules/current-state.md)),
  i.e. `NOT EXISTS` / `MINUS` / `FILTER NOT EXISTS` are conformant.
- **Rule engine.** `rdfs_closure_step` / fuelled `rdfs_closure`
  ([`RDF.Graph.Executable.fst:1139-1166`](../../formal/fstar/RDF.Graph.Executable.fst))
  and the OWL-RL closure + query rewrite
  ([`OWL.QueryRewrite.fst`](../../formal/fstar/OWL.QueryRewrite.fst))
  are forward-chaining Horn-rule engines over triples. #262 documents
  a sameAs-closure blow-up; the 10 OWL RL positive-entailment fails
  are rule-coverage gaps (out of 30).
- **Graph-level API today.** The HTTP side already speaks a
  graph-at-a-time protocol (SPARQL Graph Store Protocol,
  http-rdf-update suite 19 of 19). The npm draft
  ([`npm/factoidal/README.md`](../../npm/factoidal/README.md))
  exposes RDF/JS `DatasetCore` + `canonicalize()` but no graph-valued
  operations beyond `match(s,p,o,g)`.
- **Owner-stated durable-UPDATE direction** (task #24 in the owner's
  brief; not yet written up in-tree): COTTAS base + delta + canonical
  snapshots, built on reusable foundations. The component-graph ideas
  below are evaluated against that shape.

## 1. Literature review

### 1.1 Peirce's existential graphs (the root)

Charles Sanders Peirce's existential graphs (1890s–1910s) are a
diagrammatic logic: propositions are drawn on a *sheet of assertion*;
drawing a graph on the sheet asserts it; a closed curve (*cut*)
around a subgraph negates it; a *line of identity* denotes an
existentially quantified individual. The Alpha system is
propositional logic, Beta adds lines of identity and is equivalent to
first-order logic with equality, Gamma sketches modal extensions.
**[memory — standard history; see Sowa's edition of Peirce MS 514,
which the RDF Surfaces spec itself links,
<http://www.jfsowa.com/peirce/ms514.htm> [web: linked from the CG
spec]]** Two properties carry over to everything below:

1. **Scope is spatial.** A quantifier's scope is the surface region
   it is drawn on; nesting depth (even/odd number of enclosing cuts)
   determines whether a line of identity reads as ∃ or ∀.
2. **Negation is the only connective.** Conjunction is juxtaposition
   on a surface; everything else (∨, →, ∀) is derived from nested
   cuts.

### 1.2 Hayes' Blogic keynote (ISWC 2009)

Pat Hayes' invited talk "BLOGIC, or now what's in a link?" (ISWC
2009, Chantilly VA) — self-described as "RDF redux" — argued that
RDF's model theory got blank nodes wrong by treating a graph as a
Platonic set of triples, and proposed re-founding RDF on surfaces.
**[web: slides at
<https://www.slideshare.net/PatHayes/blogic-iswc-2009-invited-talk>;
conference page
<http://iswc2009.semanticweb.org/wiki/index.php/ISWC_2009_Keynote/Pat_Hayes.html>;
contemporaneous notes by Ian Dickinson,
<https://www.iandickinson.me.uk/blog/2009-10-27/iswc-keynote-pat-hayes-raw-notes.html>]**
Per those notes **[web]**:

- "Blank nodes in RDF are broken" — the set-theoretic abstraction
  gives bnodes no syntactic scope, which is why copying graphs
  between documents, merge-vs-union, and graph signing are all
  awkward.
- The fix: an RDF graph is *a graph plus a surface it is written on*;
  blank nodes are marks on that surface with the surface as their
  scope. This "doesn't operationally change any existing RDF".
- Surface *types* carry semantics: a positive surface asserts, a
  negative surface denies; other types can be neutral (quotation) or
  deprecated.
- Allowing surfaces to nest gives full first-order semantics, "like
  Peirce's existential graphs"; RDFS then becomes an abbreviation
  layer rather than a separate logic.
- The construction was pitched as also grounding named graphs and
  resolving the copy-vs-merge confusion.

The blank-node scoping half of the diagnosis was independently
substantiated by Hogan, Arenas, Mallea, Polleres, "Everything You
Always Wanted to Know About Blank Nodes" (JWS 2014) **[memory]**, and
is visible in this repo as standing priority 2d (per-file bnode
scoping at dataset load,
[`docs/claude-rules/current-state.md`](../claude-rules/current-state.md)).

### 1.3 The N3 lineage (what surfaces grew out of, syntactically)

- Berners-Lee, Connolly, Kagal, Scharf, Hendler, "N3Logic: A logical
  framework for the World Wide Web" (Theory and Practice of Logic
  Programming 8(3):249-269, 2008). N3 extends RDF with *graph terms*
  (`{ ... }` formulas), universal (`@forAll` / `?x`) and existential
  quantification, and `log:` builtins including `log:implies`; the
  design goal is "a minimal extension to the RDF data model such that
  the same language can be used for logic and data". **[web:
  <https://arxiv.org/pdf/0711.1533>, Cambridge TPLP entry]**
- The Notation3 Community Group specification (editors Arndt, Van
  Woensel, Tomaszuk, Kellogg; draft CG report,
  <https://w3c.github.io/N3/spec/>) is the current normative-ish
  reference. **[web: cited as the biblio entry of the RDF Surfaces
  spec]** "Existential Notation3 Logic" (TPLP, Cambridge) formalizes
  a core of N3's quantification. **[web-listed; authors Arndt and
  Mennicke [memory]]**
- Verborgh, De Roo, "Drawing Conclusions from Linked Data on the Web:
  The EYE Reasoner" (IEEE Software 32(3):23-27, 2015). EYE (Euler Yet
  another proof Engine, Prolog-based) does forward and backward
  chaining over N3 rules along Euler paths ("don't step in your own
  steps"). **[web:
  <https://ieeexplore.ieee.org/document/7093047/>, PDF at
  <https://josd.github.io/Papers/EYE.pdf>]**

N3's `{ ... }` formulas are *quoted, term-level graph literals* —
scoped contexts inside one document — which makes N3 the syntactic
ancestor of both RDF Surfaces (§1.4) and, more loosely, RDF-star
(§1.6).

### 1.4 RDF Surfaces (the modern Blogic line, 2022–2025)

**Spec.** "RDF Surfaces Primer", W3C Community Group draft (editors
Hochstenbach and De Roo, KNoWS/IMEC UGent;
<https://w3c-cg.github.io/rdfsurfaces/>). Read in full this session
from a clone of `w3c-cg/rdfsurfaces` **[web]**. The design, verbatim
from the spec's structure:

- A surface is "a kind of sheet of paper on which RDF graphs can be
  written". Blank nodes are "graffiti… engraved into the piece of
  paper and can't be transferred"; copying a graph to another surface
  requires fresh graffiti — Hayes' bnode-scoping fix made concrete.
- Syntax is a Notation3 sublanguage: a surface is a triple whose
  subject is a *graffiti list* of blank nodes, whose predicate names
  the surface kind, and whose object is a graph term. The one
  built-in with normative semantics is `log:onNegativeSurface`
  (plus `log:onNegativeAnswerSurface` for queries; positive surfaces
  are double negation). Example from the spec:

  ```
  ( _:S ) log:onNegativeSurface {
      _:S a ex:City .
      () log:onNegativeSurface {
          _:S a ex:HumanCommunity .
      } .
  } .
  ```

  reads "every city is a human community" — a Horn rule as
  `NOT (body AND NOT head)`, exactly Peirce's encoding of
  implication.
- Quantification by nesting parity: a blank node marked on an
  evenly-nested surface is existential, on an oddly-nested surface
  universal (`NOT ∃ x P(x) ⇔ ∀ x NOT P(x)` is quoted in the spec).
  Conjunction is juxtaposition; disjunction is sibling negative
  surfaces inside a negative surface; the default document surface is
  positive, which recovers exactly RDF 1.1 simple semantics for plain
  RDF.
- Coreference rules: nested surfaces cannot share blank nodes except
  by graffiti coreference to an ancestor's graffiti list; regraffiti
  on a nested surface shadows the outer mark.

**Papers.**

- Hochstenbach, De Roo, Verborgh, "RDF Surfaces: Computer Says No"
  (ESWC 2023 TrusDeKW workshop, CEUR-WS Vol-3443,
  <https://ceur-ws.org/Vol-3443/ESWC_2023_TrusDeKW_paper_134.pdf>) —
  the position paper: the goal is to "translate Hayes' BLOGIC vision
  into a concrete RDF syntax" and enable expressing "no" (denial,
  refutation) at web scale. **[web-listed]**
- Hochstenbach, van Noort, Arndt, Martens, De Roo, Verborgh, Bonte,
  Ongenae, "RDF Surfaces: Enabling Classical Negation on the Semantic
  Web" (arXiv:2406.10659, 2024; under review at the Semantic Web
  Journal, swj3708). Positions RDF Surfaces as RDF + classical
  negation + explicit existential quantification via Peirce graphs,
  with use cases in academic publishing and eHealth. **[web:
  <https://arxiv.org/abs/2406.10659>]**
- Hochstenbach et al., "RDF Surfaces as a First-Order Language for
  the Semantic Web" (Rules and Reasoning / RuleML+RR 2024, Springer
  LNCS, doi:10.1007/978-3-031-72407-7_15) — the FOL-expressivity
  treatment. **[web-listed; author list beyond Hochstenbach
  [memory]]**

**Implementations and tests.** The
`eyereasoner/rdfsurfaces-tests` repo (cloned and read this session
**[web]**) lists five implementations it drives: EYE (v11.4.6),
Latar (KNowledgeOnWebScale), tension.js (joachimvh), rs2fol
(RebekkaMa — translation of surfaces to TPTP for first-order provers)
and juliett (phochste). The suite has 99 files under `test/pure`
(pure surfaces logic, including `_FAIL` contradiction cases), plus
`built-in`, `n3support`, and `scoped-quantification` groups —
real, on-disk test files in the sense of iron rule #6, though not
W3C-manifest-shaped. A browser demonstrator runs EYE JS
(<https://w3c-cg.github.io/rdfsurfaces/demonstrator/>) **[web-listed]**;
"EYE JS: A client-side reasoning engine supporting Notation3, RDF
Surfaces and RDF Lingua" (2024) describes the client-side engine.
**[web-listed]**

### 1.5 Named graphs and dataset semantics (the other half of Blogic's audience)

- Carroll, Bizer, Hayes, Stickler, "Named Graphs, Provenance and
  Trust" (WWW 2005) and the JWS 2005 journal version "Named graphs":
  named graphs get an abstract syntax (a set of (name, graph) pairs),
  a formal semantics, TriX/TriG syntaxes, and a provenance/trust
  application built on the Semantic Web Publishing vocabulary.
  **[web:
  <https://dl.acm.org/doi/10.1145/1060745.1060835>]** The
  accompanying `rdfg:` vocabulary
  (`http://www.w3.org/2004/03/trix/rdfg-1/`) defines `rdfg:Graph`,
  `rdfg:subGraphOf`, `rdfg:equivalentGraph` — a ready-made (if
  little-used) containment vocabulary between graphs. **[memory]**
- Zimmermann (ed.), "RDF 1.1: On Semantics of RDF Datasets" (W3C
  Working Group Note, 25 Feb 2014,
  <https://www.w3.org/TR/rdf11-datasets/>): the RDF WG deliberately
  standardized *no* dataset semantics — the Note surveys seven
  options for what a graph name denotes (nothing; the graph; the
  (name, graph) pair; a context; a dereferenceable resource; quads;
  quoted graphs) because none reached consensus. **[web]** The
  operational consequence: **the relation between named graphs in a
  dataset is semantically unconstrained**, so a layered
  containment/composition vocabulary over named graphs contradicts
  nothing in RDF 1.1 or SPARQL 1.1.
- SPARQL 1.1 fixes only the *query-time* structure: a dataset is one
  default graph plus named graphs; `GRAPH` re-scopes matching;
  `FROM`/`FROM NAMED` compose the active dataset from graph IRIs.
  This is exactly the shape of our `rdf_dataset`
  ([`RDF.Graph.Executable.fst:151-154`](../../formal/fstar/RDF.Graph.Executable.fst)).

### 1.6 Nested/quoted triples: RDF-star and RDF 1.2

- Hartig, Thompson, "Foundations of an Alternative Approach to
  Reification in RDF" (arXiv 2014) and Hartig's RDF*/SPARQL* line
  (AMW 2017) introduced triple-valued terms `<<s p o>>`; the RDF-star
  Community Group report (2021) gave them a quotation-flavoured
  (referentially opaque-leaning) reading. **[memory]**
- The RDF-star Working Group (chartered 2022) folded this into RDF
  1.2: "RDF 1.2 Concepts and Abstract Data Model"
  (<https://www.w3.org/TR/rdf12-concepts/>) has *triple terms*
  (`<<( s p o )>>`) which are **transparent** (terms inside a triple
  term denote what they denote when asserted) and *reifiers*
  (`rdf:reifies`, with `<< s p o >>` as sugar for a reifying triple);
  the meaning of `rdf:reifies` is deliberately generic, and the
  definitional debate is visible in the WG tracker (e.g.
  w3c/rdf-star-wg issue #169, "definition of reifiers is
  non-normative and seems vague"). **[web-listed: TPAC 2024 overview
  by Lassila; WG issue; TR page]**
- Placement relative to the rest of this review: RDF 1.2 nests at the
  **term** level (a triple inside a triple), named graphs group at
  the **dataset** level (flat, no nesting), and N3/Surfaces nest at
  the **graph** level (a graph inside a graph, with quantifier
  scope). These are three different mechanisms and none subsumes
  another:

  | mechanism | nesting unit | scoping/negation | standard status |
  |---|---|---|---|
  | named graphs | graph in dataset | none (unspecified semantics) | RDF 1.1/1.2, SPARQL 1.1 |
  | triple terms / reifiers | triple in triple | none (transparent) | RDF 1.2 (in progress) |
  | N3 formulas | graph term | quotation + rules | CG draft |
  | RDF Surfaces | surface (graph+graffiti) | classical negation, ∃/∀ by parity | CG draft |

  COTTAS v1 already anticipates the first row (`g` column) and
  explicitly defers the second (§10 of
  [`docs/cottas-format-v1.md`](../cottas-format-v1.md)).

### 1.7 Graphs as first-class storage units ("millions of small graphs")

- **Nanopublications.** Groth, Gibson, Velterop, "The anatomy of a
  nanopublication" (Information Services & Use, 2010) **[memory]**;
  operationalized by Kuhn et al., "Publishing without Publishers: a
  Decentralized Approach to Dissemination, Retrieval, and Archiving
  of Data" (ISWC 2015 line, arXiv:1411.2749) **[web-listed]**. Each
  nanopublication is a tiny RDF **dataset** of four named graphs
  (head, assertion, provenance, publicationInfo), identified by a
  Trusty URI — the hash of its canonicalized content (Kuhn,
  Dumontier, ESWC 2014, arXiv:1401.5775, already reviewed in
  [`2026-07-03-shapes-canon-storage-strategies.md`](2026-07-03-shapes-canon-storage-strategies.md)
  §3.1). The public nanopub network holds tens of millions of such
  graphs **[memory — order of magnitude]**. This is the closest
  existing practice to the owner's "millions of component graphs,
  each instantiating a pattern": the *pattern* is the nanopub
  template, the *identity* is a canonical content hash, and the
  *composition* is a fixed 4-graph star around a head graph.
- **Semantic units.** Vogt, Kuhn, Hoehndorf, "Semantic Units:
  Organizing knowledge graphs into semantically meaningful units of
  representation" (arXiv:2301.01227, 2023; journal version in J.
  Biomedical Semantics 2024 **[memory]**): partition a KG into
  *statement units* (smallest meaningful propositions, one or more
  triples) and *compound units* (collections of units), each unit
  "implemented as its own resource" and functioning "similarly to
  named graphs"; claimed benefits include subgraph matching, KG
  profiling, and access control at unit granularity. **[web:
  abstract]** This is the owner's "graphs with substructure" as an
  explicit modelling discipline, including the units-contain-units
  composition level.
- **Relational/XML provenance of components.** R2RML (W3C Rec 2012)
  maps SQL rows to triples and its `rr:graphMap` assigns the output
  of a triples map to named graphs — per-row named graphs are a
  supported, standard pattern, i.e. "component graph = materialised
  view of a SQL row" already has a W3C-blessed mapping vocabulary.
  **[memory — R2RML §9]** The XML analogue (GRDDL, 2007) is defunct
  but establishes the document→graph unit. **[memory]**
- **Storage engines.** Quad stores index the graph column like any
  other key component: Virtuoso (quad table + graph-major indexes)
  **[memory]**, HDTQ ("Managing RDF Datasets in Compressed Space",
  Fernández et al., ESWC 2018) extends HDT with graph bitmaps
  **[memory]**, Oxigraph keys SPOG permutations in RocksDB
  **[memory]**. The "Easy and complex: new perspectives for metadata
  modeling using RDF-star and Named Graphs" comparison
  (arXiv:2211.16195, 2022) treats named graphs and RDF-star as
  complementary first-class metadata carriers **[web-listed]**;
  GRFusion (SIGMOD 2018) is the relational-DB version of the
  "graphs as first-class citizens" slogan, tangential here.
  **[web-listed]** None of these give named graphs *substructure*;
  they give them *indexes*. The substructure layer (containment,
  composition, shape-instantiation) is consistently left to
  vocabulary + application convention — which is good news for us:
  it can be layered without engine changes (§2).

## 2. Tie-in 1 — graphs-with-substructure as a data model

The owner's target: not "my graph is my working dataset" but named
graphs with substructure — millions of component graphs, each
instantiating a shape or mapping to a SQL row / XML document, with
composition into larger graphs. The literature (§1.5, §1.7) says the
pieces are: flat named graphs (standard), a composition vocabulary
(non-standard but unconstrained), content-addressed identity
(nanopubs/Trusty URIs), and shape-instantiation (semantic units,
R2RML row maps). Concretely for this repo:

### 2.1 Component graphs are just named graphs — SPARQL 1.1 survives untouched

Because RDF 1.1 assigns **no** semantics to graph names (§1.5,
Zimmermann Note), a *component graph* can be modelled as an ordinary
named graph plus assertions **about** it in a small companion
vocabulary, without changing `rdf_dataset`, the SPARQL evaluator, or
any suite score:

```
:component-42   a fct:Component ;
                fct:instantiates :PersonShape ;      # shape/pattern link
                fct:partOf :dataset-2026-07 ;        # composition (cf. rdfg:subGraphOf)
                fct:sourceRow "person:4711"^^xsd:string ;  # SQL/XML provenance
                fct:canonicalHash "sha256:..." .     # RDFC identity (§2.3)
```

- Queries that ignore components see the same dataset semantics as
  today; queries that want component scope use `GRAPH ?g` /
  `FROM NAMED` exactly as SPARQL 1.1 defines. Nothing in the W3C
  suites constrains inter-graph relations, so conformance (SPARQL
  631 pass, 0 fail; RDF 1031 pass, 0 fail) is not at risk by
  construction.
- Composition has two implementations, both standard-compatible:
  *virtual* (a composed graph is `FROM <c1> ... FROM <cn>` — SPARQL's
  own dataset construction is the composition operator) and
  *materialised* (a union graph written under its own name, with
  `fct:partOf` links recording the recipe). The Carroll et al. 2005
  `rdfg:subGraphOf` **[memory]** is prior art for the vocabulary; the
  nanopub head graph is prior art for the "recipe graph" pattern.
- Engine gaps this exposes (facts, not blockers):
  `lookup_named_graph` is a linear list scan
  ([`RDF.Graph.Executable.fst:159-162`](../../formal/fstar/RDF.Graph.Executable.fst))
  — fine as spec, wrong as the executable path at millions of graphs;
  the in-memory cost of ~1.2 KB/quad plus per-graph overhead needs
  measuring (§5, X1); `ng_name : iri` excludes blank-node graph
  names, acceptable for components (they should have stable names
  anyway) but a known RDF 1.1 delta; and the on-disk `GROUP BY ?g`
  bug ([`2026-07-03-e1-cs-clustering-results.md`](2026-07-03-e1-cs-clustering-results.md)
  §6.2) becomes load-bearing the moment components are real —
  per-component aggregation is the natural query shape.

### 2.2 A CS cluster is a shape-extension; component graphs make the grouping explicit

The E1 result already showed that grouping rows by discovered shape
(characteristic set) is what the storage wants: better compression,
predicate locality, selective prunes. Component graphs are the same
grouping *made explicit and named*:

- A component instantiating `:PersonShape` contains (at least) the
  star of triples the shape requires — i.e. **the extension of a CS
  is exactly the union of the components instantiating the
  corresponding shape**. The CS-clustering machinery
  ([`tools/cs_cluster_nq.py`](../../tools/cs_cluster_nq.py)) computes
  per-subject predicate sets; a component-graph corpus gets the same
  partition for free from its `g` column, plus multi-subject units
  (semantic units' compound case) that CS-per-subject cannot see.
- COTTAS layout: the `g` column **is** the component id — no format
  change, v1 already stores it. The right physical move is *not*
  row-group-per-component: at ~10-100 triples per component and
  122,880-row row groups, one row group holds thousands of
  components, and Parquet footer metadata scales with row-group
  count, so millions of row groups is a self-inflicted wound.
  Instead: sort rows by `(shape-id, component-id, s, p, o)` — the E1
  sort with the component id interposed — so each component is
  contiguous, each row group covers a contiguous run of components of
  (mostly) one shape, and three existing mechanisms light up:
  per-row-group `g` min/max ranges (Parquet column statistics,
  already tolerated by v1 §2), the per-graph Bloom sidecars
  ([`graph-bloom-sidecars.md`](graph-bloom-sidecars.md)), and the
  Yod6/compound-(p,o) presence cascade, which E1 showed becomes
  selective under shape-sorted order.
- The SQL/XML mapping story costs no new machinery: R2RML
  `rr:graphMap` **[memory]** produces exactly "one named graph per
  row"; a future `factoidal import --r2rml mapping.ttl` would emit a
  component-graph corpus whose `fct:sourceRow` provenance is written
  by the mapper. Until then, the corpus pipeline can synthesize
  component-graph corpora for measurement (§5, X1).

### 2.3 Canonical hashes give components content-addressed identity for free

This is where the repo already holds an asset the literature says is
the linchpin. Nanopublications scale to millions of graphs because
each graph's name is (derived from) its canonical content hash —
dedup, immutability, and citation come from the naming scheme (Kuhn &
Dumontier 2014). Our RDFC-1.0 implementation
([`RDF.Canonical.fst`](../../formal/fstar/RDF.Canonical.fst)) plus
the E3 plan (per-graph `c14n.sha256` sidecars + Merkle roll-ups)
means:

- `fct:canonicalHash` per component is computable today (HFDQ-only,
  decline-to-hash on ties — and components are small and mostly
  tree-shaped, precisely the "shape-bounded bnodes ⇒ cheap
  canonicalization, no HNDQ recursion" case argued in
  [`2026-07-03-shapes-canon-storage-strategies.md`](2026-07-03-shapes-canon-storage-strategies.md)
  §3.2; X2 in §5 measures the tie rate).
- Composed graphs get Merkle identities (hash of sorted child
  hashes), which is the natural persistence unit for the owner's
  durable-UPDATE shape: **base COTTAS file + delta of changed
  components + canonical snapshot = a Merkle root**. An UPDATE
  touches k components ⇒ k re-hashes + one roll-up path, not a
  corpus re-canonicalization. Component granularity is what makes
  "canonical snapshots" affordable.
- Idempotent ingest and blank-node-stable diffs (E3's claims) become
  *per-component* — the diff of two dataset versions is a set
  difference over component hashes, the OSTRICH-style delta chain's
  natural key.

## 3. Tie-in 2 — surfaces as scoped negation/quantification

### 3.1 What adopting surface-style logic would mean

RDF Surfaces adds two things RDF (and our engine) lack: **classical
negation** with an explicit scope, and **explicit quantifier scoping**
for blank nodes (§1.4). For factoidal this decomposes into layers of
very different cost:

1. **AST + parser (implementable, bounded).** A surfaces AST is a
   small mutually recursive F\* type — informally:

   ```fstar
   noeq type surface_stmt =
     | SS_Triple  : triple -> surface_stmt
     | SS_Negative: list bnode_id (* graffiti *) ->
                    list surface_stmt -> surface_stmt
   type surface_doc = list surface_stmt   (* default positive surface *)
   ```

   The syntax is an N3 sublanguage (graffiti list subject,
   `log:onNegativeSurface`, graph-term object), so the parser needs
   N3 graph terms — new grammar territory relative to our
   Turtle/TriG parsers, written in F\* first per iron rule #4. The
   `w3c-cg/rdfsurfaces` repo ships an EBNF and ANTLR grammar
   (`grammar/rdfsurfaces.ebnf`, `.g4`) **[web]** to work from, and
   `eyereasoner/rdfsurfaces-tests` provides 99 pure-logic test files
   plus scoped-quantification cases **[web]** — real on-disk tests
   per iron rule #6, though we would need to wrap them in a
   manifest-shaped runner.
2. **The rule fragment (implementable, medium).** The spec's own
   examples show that depth-≤2 nesting encodes exactly Horn rules
   (`( graffiti ) log:onNegativeSurface { body. ()
   log:onNegativeSurface { head. } }`) and queries (answer
   surfaces). That fragment is *forward-chaining over universally
   quantified rules* — operationally the same shape as
   `rdfs_closure_step`
   ([`RDF.Graph.Executable.fst:1139`](../../formal/fstar/RDF.Graph.Executable.fst))
   and the OWL-RL closure, except with rules read from data instead
   of baked into F\* constructors. A `surface_doc → list rule`
   compiler for the depth-≤2 fragment plus reuse of the existing
   fixpoint engine would execute much of `test/pure`. Two cautions
   from our own tree: the OWL-RL closure already has a measured
   blow-up (#262) that data-supplied rules would make easier to
   trigger, and fuelled termination is the right F\* discipline here
   (the general calculus is FOL, hence undecidable — rs2fol's
   existence, translating surfaces to TPTP for first-order provers
   **[web]**, is the community's admission of that).
3. **Full FOL semantics + contradiction detection (research).**
   Beyond depth 2: disjunction (sibling negative surfaces),
   contradiction reporting (the `_FAIL` tests), double-negation
   rewriting. The SWJ paper is still under review and the answer-
   surface section of the CG spec is literally marked "Issue: TODO"
   **[web]** — the semantics of query answering is not yet settled
   upstream. Building this now would be specifying against a moving
   draft. Where F\* has something distinctive to offer *later*: a
   model-theoretic semantics for the AST (interpretation functions
   over `surface_doc`) with machine-checked soundness of the rewrite
   rules — the kind of theorem the RDF Surfaces papers state on paper
   only. That is a publishable contribution, not a sprint task.

### 3.2 Relation to OWL-RL and the N3/EYE practice

EYE's ecosystem runs OWL-RL as N3 rule files over the same engine
that runs surfaces **[memory — eyereasoner distributes OWL-RL rule
sets]**; our architecture is the mirror image (rules compiled into
F\*, no rule *language* exposed). Adopting the surfaces rule fragment
would effectively give factoidal a verified rule language, and the
OWL-RL rule set could eventually be *data* validated against the same
semantics — attractive for the rule-coverage gaps behind the 10
positive-entailment fails (adding a rule becomes adding data + rerun,
not F\* surgery). That is a direction, not a plan; the near-term OWL
work (#262, PE fails) should proceed as scoped in
[`docs/claude-rules/current-state.md`](../claude-rules/current-state.md)
regardless.

### 3.3 SPARQL NOT EXISTS as today's pragmatic bridge — with the honest caveat

`FILTER NOT EXISTS` / `MINUS` (we pass negation 12 of 12) give
**negation as failure over the queried dataset**: "no matching triple
is present". A negative surface asserts **classical falsity**: "this
is false, wherever you are". The two coincide only under a
closed-world reading of the dataset. The practical bridge that is
sound today:

- Surface-style *integrity rules* of the form NOT(body) — "no
  component may contain both P and Q" — translate directly to `ASK {
  body }` expecting false, i.e. constraint checking by query. This
  is also exactly SHACL's evaluation model (`sh:not`,
  `sh:maxCount 0`), which is standing priority #5 — one more reason
  the SHACL validator and the surfaces fragment share a future core.
- Surface-encoded Horn rules (depth-2, §3.1) translate to
  CONSTRUCT-shaped forward steps, which our closure engine already
  embodies.
- What does **not** bridge: disseminating a negation to *other*
  consumers (the "computer says no" use case — refuting a claim you
  don't host). That needs the surfaces exchange syntax itself, or at
  minimum publishing the ASK-shaped constraint as data.

Component graphs (§2) and surfaces compose neatly at the vocabulary
level: a component carrying `fct:instantiates :Shape` is a positive
assertion about graph content; a surfaces layer is where "component
X **must not** match pattern P" becomes exchangeable data rather
than out-of-band convention.

## 4. Tie-in 3 — API implications (npm/JS surface and CLI)

What RDF/JS already affords
([`npm/factoidal/README.md`](../../npm/factoidal/README.md) implements
DatasetCore): `match(s, p, o, graph)` gives per-graph extraction, and
quads carry a `graph` term — so *reading* component-partitioned data
needs nothing new. What DatasetCore does not give: enumeration of
graph names, graph-level values (a Dataset per component), identity,
or composition. Candidate extensions, all thin consumers of existing
F\* machinery (no new semantics in JS, per the package's own
provenance note):

- `parseToComponent(text, {format, name?})` — parse one document into
  a dataset whose triples land in one named graph; default `name` =
  canonical hash (`c14n:sha256:...`), i.e. the Trusty-URI pattern.
  Uses existing parse + RDFC.
- `components(ds)` / `component(ds, name)` — enumerate named graphs /
  project one component as a Dataset. Pure accessor over
  `ds_named`.
- `canonicalId(ds | component)` — per-graph RDFC hash; the existing
  `canonicalize()` covers the whole dataset, this is its graph-scoped
  sibling (must inherit E3's decline-on-HFDQ-tie rule).
- `compose(...components, {name?})` — union with bnode freshness
  (the `rename_*_bnodes` helpers at
  [`RDF.Graph.Executable.fst:168-187`](../../formal/fstar/RDF.Graph.Executable.fst)
  exist precisely for this), recording `fct:partOf` provenance
  triples if asked.
- Query with component provenance — already expressible as
  `SELECT ... WHERE { GRAPH ?g { ... } }`; the API note is
  documentation plus, later, an option to auto-wrap a pattern in
  `GRAPH ?g` and surface `?g` per binding.
- CLI: `factoidal canonicalize --per-graph` (extends standing
  priority #6), `factoidal component split|compose` for the
  explode/compose transforms used in X1. The Graph Store Protocol
  side (19 of 19) already PUTs/GETs named graphs over HTTP — the
  component API is the same operation set at CLI/JS level.

Not proposed: a surfaces API in npm before the F\* AST exists (rule
#7 — no JS-side logic), and no RDF/JS `DatasetCore` deviation —
extensions above are additive functions, not interface changes.

## 5. Ranked experiments (measurement plans, not commitments)

### X1 — Component-graph corpus on COTTAS: does `g`-as-component-id scale?

**Hypothesis:** a corpus exploded into per-record component graphs
(`g` = component IRI), row-sorted by `(shape, component, s, p, o)`,
(1) costs little in file size versus the monolithic default-graph
build, (2) makes `GRAPH`-scoped queries prunable via per-row-group
`g` ranges + the existing graph-Bloom sidecars, and (3) exposes the
first real scaling wall (linear `lookup_named_graph`, per-graph
memory overhead) with numbers attached.

**Build:** a producer-side script (in-policy per
[`docs/cottas-format-v1.md`](../cottas-format-v1.md) §1) that
converts a corpus into components — ukparliament grouped per subject
record, or the E1 synthetic generator emitting one named graph per
subject — then writes both variants with the E1 scratchpad writer
(which already preserves row order and forces DLBA). Rebuild the
graph-Bloom sidecars for the component build.

**Measure:** (1) `.cottas` + sidecar sizes, component vs monolithic;
(2) wall time for `GRAPH <c>`-bound point queries, `GRAPH ?g` scans,
and star queries, 3+ runs, median (min-max), via the E1 method;
(3) row groups pruned vs scanned with `g` statistics + Bloom
sidecars; (4) in-memory load RSS at 10k / 100k / 1M components (the
1.2 KB/quad baseline is per-quad — the per-graph increment is the
unknown); (5) correctness:
[`tests/local/backend_parity_regressions.sh`](../../tests/local/backend_parity_regressions.sh)
unchanged, plus in-memory ground truth for every on-disk number.
**Prerequisites:** the two bugs E1 filed are on this path — the §6.1
RLE_DICTIONARY multi-row-group decode failure and, especially, §6.2
`GROUP BY ?g` returning wrong counts, which is *the* component
aggregation query. Fixing 6.2 is part of X1's definition of done.
**Cost:** small-to-medium (producer script + bench session + one
evaluator bug). **Risk:** millions of tiny graphs may hit the linear
named-graph lookup first and drown the storage signal — that is a
finding, not a failure; record it and it scopes the fix.

### X2 — Per-component canonical hashes: E3 at component granularity

**Hypothesis:** RDFC (HFDQ-only) canonicalization of small
shape-instantiating components is near-linear with an HFDQ-tie rate
of ~0, making content-addressed component names
(`fct:canonicalHash`, Merkle roll-up per composed graph / corpus)
affordable at millions-of-components scale — the substrate for the
durable-UPDATE base+delta+snapshot shape.

**Build:** rides E3 and standing priority #6 (`factoidal
canonicalize` CLI): add `--per-graph` emission over an X1 component
corpus; a roll-up script mirroring
[`tools/graph_bloom_rollup.py`](../../tools/graph_bloom_rollup.py).
**Measure:** (1) canonicalization throughput (components/s and
quads/s) vs component size; (2) HFDQ-tie frequency (predicted ~0 for
tree-shaped components — this is the empirical check of the
shape-bounded-bnodes claim, per-corpus); (3) incremental-rebuild wall
time: change k of N components, re-derive the corpus Merkle root,
k ∈ {1, 100, 10k}; (4) rdf-canon suite unchanged (62 pass, 23 fail,
1 skip of 86 baseline). **Cost:** small once #6 lands. **Risk:**
HFDQ ties on components that share bnode structure — covered by the
decline-to-hash rule; measure, don't assume.

### X3 — Surfaces micro-prototype: F\* AST + the depth-≤2 rule fragment

**Hypothesis:** a surfaces AST in F\* plus a compiler from the
depth-≤2 `log:onNegativeSurface` fragment to the existing
forward-chaining engine executes a labelled subset of
`eyereasoner/rdfsurfaces-tests test/pure` correctly, at a module cost
comparable to one parser (and tells us the real cost of N3 graph
terms in our parser stack).

**Build:** `RDF.Surfaces.fst` (AST + depth-≤2 rule extraction; parser
for the N3S subset working from the CG repo's EBNF); a runner mapping
`test/pure` inputs to expected outputs (the repo drives EYE/Latar/
rs2fol via `make_examples.sh` — we mirror that, not W3C manifests).
Explicitly out of scope: disjunction, contradiction (`_FAIL` cases),
answer-surface semantics beyond the rule pattern (upstream spec
marks answer surfaces "TODO").
**Measure:** pass/fail over the attempted subset, labelled ("N pass,
M fail, K out-of-fragment (out of 99 pure tests)" — anti-pattern
#25); parser + closure wall time; and a written go/no-go on deeper
nesting. **Cost:** medium (one parser + one compiler + runner).
**Risk:** spec instability upstream (SWJ paper under review, spec
TODOs) — contained by scoping to the fragment the spec's own examples
fix; rule-engine blow-ups — contained by fuel + the #262 lesson.

**Ranking rationale:** X1 first — it advances the owner's
graphs-over-triples refocus on the axis where the repo already has
harnesses (E1's writer and bench method, Bloom sidecars) and its
prerequisite bug fixes are needed anyway. X2 second — mostly rides
work that is already standing priority #6/E3, and it is the piece the
durable-UPDATE shape depends on. X3 third — it is the research-
flavored one; do it when a session wants a self-contained new-module
project, not on the storage critical path.

## 6. Web sources consulted

- Hayes 2009, BLOGIC (ISWC invited talk) slides:
  <https://www.slideshare.net/PatHayes/blogic-iswc-2009-invited-talk>;
  conference page:
  <http://iswc2009.semanticweb.org/wiki/index.php/ISWC_2009_Keynote/Pat_Hayes.html>;
  contemporaneous notes (Dickinson):
  <https://www.iandickinson.me.uk/blog/2009-10-27/iswc-keynote-pat-hayes-raw-notes.html>
- RDF Surfaces Primer (W3C CG draft, Hochstenbach & De Roo) — read
  from a clone of <https://github.com/w3c-cg/rdfsurfaces> (index.bs,
  grammar/, examples/)
- RDF Surfaces test suite — read from a clone of
  <https://github.com/eyereasoner/rdfsurfaces-tests> (99 pure tests;
  drives EYE, Latar, tension.js, rs2fol, juliett)
- Hochstenbach et al. 2024, RDF Surfaces: Enabling Classical Negation
  on the Semantic Web: <https://arxiv.org/abs/2406.10659> (SWJ
  submission: <https://www.semantic-web-journal.net/system/files/swj3708.pdf>)
- Hochstenbach, De Roo, Verborgh 2023, RDF Surfaces: Computer Says
  No (ESWC TrusDeKW):
  <https://ceur-ws.org/Vol-3443/ESWC_2023_TrusDeKW_paper_134.pdf>
- Hochstenbach et al. 2024, RDF Surfaces as a First-Order Language
  for the Semantic Web (RuleML+RR, LNCS):
  <https://link.springer.com/chapter/10.1007/978-3-031-72407-7_15>
- Berners-Lee, Connolly, Kagal, Scharf, Hendler 2008, N3Logic (TPLP):
  <https://arxiv.org/pdf/0711.1533>
- Notation3 CG spec (Arndt, Van Woensel, Tomaszuk, Kellogg, draft):
  <https://w3c.github.io/N3/spec/>
- Verborgh, De Roo 2015, The EYE Reasoner (IEEE Software):
  <https://ieeexplore.ieee.org/document/7093047/>,
  <https://josd.github.io/Papers/EYE.pdf>
- Carroll, Bizer, Hayes, Stickler 2005, Named Graphs, Provenance and
  Trust (WWW): <https://dl.acm.org/doi/10.1145/1060745.1060835>
- Zimmermann 2014, RDF 1.1: On Semantics of RDF Datasets (W3C Note):
  <https://www.w3.org/TR/rdf11-datasets/>
- RDF 1.2 Concepts and Abstract Data Model (W3C, in progress):
  <https://www.w3.org/TR/rdf12-concepts/>; reifier-definition debate:
  <https://github.com/w3c/rdf-star-wg/issues/169>; overview (Lassila,
  TPAC 2024):
  <https://www.lassila.org/publications/2024/TPAC2024/RDF-star-intro/Overview.html>
- Vogt, Kuhn, Hoehndorf 2023, Semantic Units:
  <https://arxiv.org/abs/2301.01227>
- Kuhn et al. 2014, Publishing without Publishers (nanopub network):
  <https://arxiv.org/pdf/1411.2749>
- Easy and complex: RDF-star and Named Graphs (2022):
  <https://arxiv.org/abs/2211.16195>
- RDF Surfaces demonstrator (EYE JS):
  <https://w3c-cg.github.io/rdfsurfaces/demonstrator/>

From-memory citations needing verification before load-bearing use:
Peirce EG systems (Alpha/Beta/Gamma) and Sowa's MS 514 commentary;
Hogan et al. 2014 blank-nodes survey (JWS); the `rdfg:` vocabulary
(`rdfg:subGraphOf`) from the 2005 named-graphs work; R2RML
`rr:graphMap` (W3C Rec 2012 §9); Groth, Gibson, Velterop 2010 anatomy
of a nanopublication; HDTQ (ESWC 2018); Virtuoso/Oxigraph graph
indexing details; Hartig & Thompson 2014 / Hartig 2017 RDF-star
foundations and the 2021 CG report's opacity stance; EYE's OWL-RL
rule distribution; author lists for "Existential Notation3 Logic"
and "EYE JS".
