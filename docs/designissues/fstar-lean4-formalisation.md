# Formalising W3C RDF 1.1 Concepts in F* and Lean 4

## Executive summary

This report surveys formal and semi-formal artefacts in **F\*** and **Lean 4** that implement or mechanise *core* W3C **RDF 1.1** concepts: RDF terms (IRIs, literals, blank nodes), triples, graphs, datasets, graph/dataset comparison (isomorphism), RDF semantics (simple/RDF/RDFS entailment), SPARQL entailment regimes, and concrete syntaxes (Turtle, TriG, N-Triples, N-Quads, RDF/XML, JSON-LD). It maps each concept to the relevant *normative* spec sections and then cross-maps discovered implementations to those sections.

The core finding is that **Lean 4 has a practical RDF library (RDF.lean) that implements the data model and I/O (parsing/serialisation) but does not mechanise the RDF 1.1 model-theoretic semantics or entailment**. No *F\** projects were identified whose primary scope is an RDF 1.1 formalisation (definitions + proofs) on the scale of the W3C specs.

Because semantics/entailment and graph isomorphism are the most "proof-heavy" components, the closest mechanised baseline is **CoqRDF** (a Coq + Mathematical Components development) authored by Tomas Vallejos and Assia Mahboubi with a supporting thesis at Universidad de Chile. CoqRDF explicitly targets RDF 1.1 abstract syntax and mechanises operations including **blank node relabelling and RDF graph isomorphism**, plus an iso-canonicalisation algorithm (kappa-mapping) with proofs (in the thesis).

For next steps, the recommended strategy is a staged formalisation: (i) **core abstract syntax** + well-formedness, (ii) **graph equivalence/isomorphism** and (optionally) dataset comparison, (iii) **a mechanised entailment engine** (rule closure) with soundness/completeness relative to RDF 1.1 Semantics, and only later (iv) verified parsing -- initially relying on W3C test suites and trusted external parsers (via extraction/FFI) rather than proving parser correctness end-to-end.

A contextual note, given the current date (2026): RDF 1.2 publications now exist and explicitly **supersede** parts of the RDF 1.1 suite (e.g., RDF 1.2 Semantics supersedes the 2014 Semantics document). This report nevertheless anchors on RDF 1.1 as requested and treats RDF 1.2 as "scope drift to watch".

## RDF 1.1 concepts to formalise and normative anchors

### Core RDF abstract syntax and comparison

The RDF 1.1 **Concepts and Abstract Syntax** recommendation defines the foundational entities: RDF triples, IRIs, literals, blank nodes, and RDF graphs/datasets, along with comparison notions. Its structure is particularly amenable to formalisation because the main definitions are algebraic (sets of triples, etc.), while comparison introduces existential structure (blank node renaming) that drives most proof obligations.

The following table gives a concept-by-concept map to the *exact* RDF 1.1 spec sections (and, where applicable, Semantics and syntax specs).

| Concept to formalise | RDF 1.1 Concepts section | RDF 1.1 Semantics section | Concrete syntax / processing sections (non-exhaustive) |
|---|---|---|---|
| RDF triple (subject, predicate, object) | 3.1 "RDF Triples" | Used throughout; core interpretation/entailment definitions build on graphs of triples | N-Triples 2.1 "Simple Triples"; Turtle grammar 6 and parsing 7 |
| IRI / IRI reference | 3.2 "IRIs" | Interpreted as IRIs in vocabulary and semantic conditions; see also skolemisation discussion | Turtle 6.3 "IRI References"; TriG 4.3 "IRI References"; N-Triples 2.2 "IRIs" |
| Literal (lexical form, datatype IRI, language tag) | 3.3 "Literals" and 5 "Datatypes" | 7 "Literals and datatypes" (incl. datatype entailment) | Turtle list + literal construction rules in 7 "Parsing" (term constructors); RDF/XML 2.7 xml:lang and 2.9 rdf:datatype; JSON-LD 1.0 API 10.6 "Data Round Tripping" |
| Blank node | 3.4 "Blank Nodes" | Appears in entailment (existentials); 6 "Skolemization" discusses replacing blank nodes | Turtle 7 parsing allocates fresh blank nodes for `[]` and blank node property lists; JSON-LD 1.0 API 9.3 "Generate Blank Node Identifier" |
| Skolemisation (replacing blank nodes with IRIs) | 3.5 "Replacing Blank Nodes with IRIs" | 6 "Skolemization" | -- |
| RDF graph as a set of triples | Implicit in 3; graph comparison in 3.6 | Core object of interpretation; 5 "Simple Interpretations" and onwards define truth/entailment for graphs | Turtle serialises an RDF Graph (conformance statement references 6 grammar + 7 parsing); RDF/XML "XML Syntax for RDF graphs" |
| Graph comparison and graph isomorphism | 3.6 "Graph Comparison" | Semantic equivalence/entailment relates, but isomorphism is a syntactic notion; Semantics provides entailment/equivalence framing | Often exercised via test suites rather than syntax docs; compare to canonicalisation standards (post-1.1) |
| RDF dataset (default graph + named graphs) | 4 "RDF Datasets" and 4.1 "Dataset Comparison" | 10 "RDF Datasets" defines an interpretation notion for sets of graphs, but dataset meaning is also called out as unsettled elsewhere | TriG serialises an RDF Dataset; N-Quads 4 "Grammar" + 5 "Parsing" + 5.2 "RDF Dataset Construction"; JSON-LD 1.0 API 10 |

### RDF 1.1 semantics and entailment regimes

The RDF 1.1 **Semantics** recommendation defines the core model-theoretic semantics for graphs and the entailment regimes (Simple, RDF, RDFS, plus datatype entailment). It also includes a rule-based presentation (Appendix A) and notes about completeness with a "generalised RDF" closure construction.

The minimum *semantic* target surface for a rigorous formalisation typically includes:

- **Simple entailment**: 5.2 "Simple Entailment" within 5 "Simple Interpretations"
- **RDF entailment**: 8.1 "RDF entailment" within 8 "RDF Interpretations"
- **RDFS entailment**: 9.2 "RDFS entailment" within 9 "RDFS Interpretations"
- **Datatypes / D-entailment**: 7 "Literals and datatypes" (incl. datatype entailment treatment)
- **Skolemisation** as a semantics-adjacent transformation: 6 "Skolemization"

For query answering under entailment, **SPARQL 1.1 Entailment Regimes** defines per-regime legality constraints (legal graphs/queries), behaviour on illegal inputs, and how entailment is used to extend BGP matching. Its structure is intentionally modular around regime descriptors (name/IRI/legal graphs/legal queries/entailment/inconsistency handling).

A key modelling challenge for datasets is that the W3C note **"On Semantics of RDF Datasets"** states that, while RDF graphs have a formal semantics, **there is no agreed formal semantics for RDF datasets**; it explains that a dataset is a set of (name, graph) pairs plus a distinguished default graph, and that this does not directly match the graph semantics definitions. This matters because it affects what constitutes a "correct" dataset semantics formalisation in F\*/Lean4: you must either (a) formalise only syntactic dataset comparison (as per Concepts 4/4.1), or (b) define an *additional* semantics layer and explicitly state it is a design choice rather than a direct restatement of RDF 1.1 Semantics.

## Existing formalisations in F* and Lean 4

### Search outcome

A targeted search across code repositories and community registries identified **one** Lean 4 artefact that squarely targets RDF: **RDF.lean** (GitHub user "jeswr"), which presents itself as "an RDF library for Lean 4" and provides parsing/serialisation via the Rust crate **oxrdfio**.

No similarly-scoped formalisation in **F\*** was identified: i.e., no public artefact was found that provides a mechanised formalisation of RDF 1.1 terms/graphs/semantics with proofs in F\*.

### Comparison table of discovered F\*/Lean4 artefacts

| Artefact | Language | Status | Scope claim | Mapping to W3C RDF 1.1 sections | Licence |
|---|---|---|---|---|---|
| RDF.lean | Lean 4 + Rust (FFI bridge) | Executable definitions + I/O; defines term/triple structures and provides IO functions `RDFParse` returning `Array Triple` | Data model: subjects as named node or blank node; triples as record; literals include typed and language-tagged encodings at the Rust boundary. Parsing/serialisation delegates to oxrdfio (supports Turtle, TriG, N-Triples, N-Quads, RDF/XML, JSON-LD 1.0) | Core abstract syntax aligns with Concepts 3.1-3.4 (Triples/IRIs/Literals/Blank Nodes). Parsing relates to Turtle 6-7 and other syntaxes per oxrdfio's supported formats list. Dataset-level syntaxes are parsed as quads in Rust but exposed as triples in Lean (graph name information not represented in the Lean API) | MIT |
| No qualifying F\* RDF 1.1 formalisation identified | F\* | -- | -- | -- | -- |

### Analytical notes on RDF.lean's coverage vs the RDF 1.1 surface

RDF.lean clearly covers the *core syntactic* layer: it defines `Subject` as either `NamedNode` or `BlankNode`, and a `Triple` record with subject/predicate/object fields (with JSON encoders/decoders and decidable equality derived). The public parsing API `RDFParse` returns `Except String (Array Triple)`, indicating the library's primary graph representation is "a list/array of triples", rather than a quotient by set equality (duplicate-free sets) as in the W3C abstract model.

Crucially for "deep" W3C RDF 1.1 coverage, RDF.lean provides **no mechanised RDF 1.1 semantics (simple/RDF/RDFS entailment) nor graph/dataset isomorphism proofs**: it is best characterised as a pragmatic Lean 4 data model + I/O layer, with semantics/reasoning left to future work or external tooling.

## Closest work outside F* and Lean 4

Given the gaps in F\*/Lean4 for semantics and graph isomorphism, the most relevant neighbouring work comes from **Coq**, **Agda**, and functional-language libraries (OCaml/Haskell/Rust) that implement RDF toolchains without mechanised proofs.

### Closest artefacts

| Artefact | System | What it covers | Licence |
|---|---|---|---|
| CoqRDF library | Coq (with Mathematical Components) | Defines RDF graphs as duplicate-free sequences of triples; includes operations such as blank node relabelling and RDF isomorphism | Unspecified |
| "A Coq formalization of RDF" thesis (UChile) | Academic (Coq formalisation) | Adopts RDF 1.1 abstract syntax; formalises RDF equality/isomorphism and proves properties; implements and verifies kappa-mapping iso-canonicalisation algorithm | Unspecified |
| Agda Semantic Web Libraries | Agda | Intends to support semantic web data in Agda; states RDF + OWL semantics via description logics in `Web.Semantic.DL` | MIT |
| OCaml-RDF | OCaml | Manipulates RDF graphs; supports reading/writing Turtle, RDF/XML, N-Quads; includes SPARQL support | LGPL-3.0 |
| rdf4h | Haskell | RDF library with parsers/serialisers for N-Triples and Turtle and an RDF/XML parser; includes IRI parsing/resolution | Unspecified |
| OxRDF / OxRDF I/O | Rust | Data structures encoding RDF 1.1 concepts; oxrdfio provides parsers/serialisers for JSON-LD 1.0, Turtle, TriG, N-Triples, N-Quads, RDF/XML | MIT / Apache-2.0 |

### Portability to F* and Lean 4 by concept

| RDF concept | Best reference starting point | Porting to Lean 4 | Porting to F\* | Main technical challenges |
|---|---|---|---|---|
| IRIs | W3C Concepts 3.2 + syntax specs | Low-Medium | Low-Medium | Decide whether to model IRIs abstractly vs fully implement RFC 3987/3986 handling |
| Literals + datatypes | W3C Concepts 3.3/5 and Semantics 7 | Medium-High | Medium | Datatype semantics requires modelling lexical-to-value-space mappings |
| Blank nodes | W3C Concepts 3.4 and Semantics 6 | Medium | Medium | Representing blank nodes as existentials while supporting decidable equality |
| Triples and graphs | W3C Concepts 3.1 | Low | Low | Choosing canonical internal representation (multiset/list vs finite set) |
| Graph comparison / isomorphism | W3C Concepts 3.6; CoqRDF | Medium-High | Medium-High | Requires bijections over blank nodes and reasoning about renaming invariance |
| RDF datasets + dataset comparison | W3C Concepts 4/4.1 | Medium-High | Medium | Dataset semantics is explicitly unsettled in RDF 1.1 |
| Simple entailment | RDF 1.1 Semantics 5.2 | Medium | Medium | Core is graph homomorphism/substitution |
| RDF and RDFS entailment (rule closure) | RDF 1.1 Semantics 8.1, 9.2; Appendix A | High | Medium-High | Mechanising model theory is substantial; rule-closure characterisation is more executable |
| SPARQL entailment regimes | SPARQL 1.1 Entailment Regimes spec | High | Medium-High | Adds regime-specific legality constraints and behaviour on inconsistency |
| Parsing/serialisation (verified) | W3C Turtle 6-7; N-Quads 4-5; JSON-LD 1.0 API 10 | Very High | High | Proving parser implements complex grammar and produces exact abstract RDF |

## Recommended next steps

### Recommended priority order

1. **Core abstract syntax + well-formedness**: IRIs, literals, blank nodes, triples, graphs, datasets, with explicit mapping to Concepts 3-5
2. **Graph comparison and isomorphism**: implement Concepts 3.6 and prove it is an equivalence relation; add dataset comparison from 4.1 if datasets are in scope
3. **Simple entailment**: mechanise Semantics 5.2 as a substitution/homomorphism relation and prove basic meta-properties
4. **RDF and RDFS entailment via closure rules**: implement a forward-chaining closure for the RDF/RDFS rules, then prove soundness/completeness against the model theory (Semantics 8-9)
5. **Concrete syntax integration**: wire in parsing/serialisation through a trusted library and validate via W3C tests; treat this layer as "trusted computing base" initially

### Suggested module boundaries

- **Rdf.Term**: IRI, BlankNode, Literal, Term constructors; invariants from Concepts 3.2-3.4 and Semantics 7
- **Rdf.Triple**: triple typing constraints (predicate must be IRI; subject cannot be literal), Concepts 3.1
- **Rdf.Graph**: graphs as finite sets; set equality and operations
- **Rdf.GraphIso**: bnode renaming, isomorphism, canonicalisation hooks (influenced by CoqRDF thesis)
- **Rdf.Dataset**: default graph + named graphs; dataset comparison (4.1)
- **Rdf.Semantics**: interpretations and entailment relations (Simple/RDF/RDFS)
- **Rdf.Syntax**: trusted parsing/serialisation wrappers; test harnesses

### Module dependency diagram

```
Term (IRI, BlankNode, Literal)
  |
  v
Triple
  |
  v
Graph <--- GraphIsomorphism
  |
  |---> SimpleEntailment ---> RDFEntailment ---> RDFSEntailment
  |
  v
Dataset <--- DatasetComparison
  |
  v
Syntax (parsers/serialisers)
```

### Proof obligations that match the W3C documents

- **Well-formedness preservation**: constructors and transforms (skolemisation, bnode renaming) preserve RDF well-formedness constraints
- **Isomorphism is an equivalence relation** and is respected by graph operations (union/merge)
- **Entailment correctness**: if implementing rule closure, prove (i) soundness: closure(G) is entailed by G, and (ii) completeness: if G entails H then H is subset of closure(G) under the required conditions
- **Test-suite conformance bridging**: connect semantics/entailment implementation with W3C entailment test suites

### F* skeleton for key concepts

```fstar
module Rdf.Core

open FStar.Set

type iri = s:string

type bnode_id = nat

type langtag = string

type literal =
  | Typed  : lex:string -> dt:iri -> literal
  | Lang   : lex:string -> tag:langtag -> literal

type term =
  | Iri   : iri -> term
  | BNode : bnode_id -> term
  | Lit   : literal -> term

type subject =
  | S_iri   : iri -> subject
  | S_bnode : bnode_id -> subject

type predicate = iri

type triple = {
  s: subject;
  p: predicate;
  o: term
}

type graph = set triple

type bnode_map = bnode_id -> bnode_id

val rename_term   : bnode_map -> term    -> term
val rename_subj   : bnode_map -> subject -> subject
val rename_triple : bnode_map -> triple  -> triple
val rename_graph  : bnode_map -> graph   -> graph

val iso : graph -> graph -> Type0
```

### Lean 4 skeleton for key concepts

```lean
namespace RDF

structure IRI where
  val : String
deriving DecidableEq, Repr

structure BNode where
  id : Nat
deriving DecidableEq, Repr

inductive Literal where
  | typed : (lex : String) -> (dt : IRI) -> Literal
  | lang  : (lex : String) -> (tag : String) -> Literal
deriving DecidableEq, Repr

inductive Term where
  | iri   : IRI -> Term
  | bnode : BNode -> Term
  | lit   : Literal -> Term
deriving DecidableEq, Repr

inductive Subject where
  | iri   : IRI -> Subject
  | bnode : BNode -> Subject
deriving DecidableEq, Repr

abbrev Predicate := IRI

structure Triple where
  s : Subject
  p : Predicate
  o : Term
deriving DecidableEq, Repr

abbrev Graph := Finset Triple

end RDF
```

### Practical note on JSON-LD conversion constraints

If you plan to incorporate JSON-LD parsing/serialisation while keeping RDF strictness, note that JSON-LD's normative RDF conversion algorithms explicitly discuss a mismatch: RDF disallows blank nodes as predicates, while JSON-LD can express them, and the JSON-LD to RDF algorithm discards such triples unless a "produce generalized RDF" option is enabled. This is exactly the kind of cross-spec edge case that should be captured as an explicit lemma/spec obligation in a rigorous formalisation (e.g., "conversion preserves RDF well-formedness by dropping generalised triples").
