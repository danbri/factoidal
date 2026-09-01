# Glossary of W3C architectural terms

One term, one meaning, across every specification this project
implements. Written because the same idea carries different names in
different specifications, and because several defects in this tree
came from using an everyday word where a specification term exists.

Rules for using this file:

1. In code comments, commit messages, issue text and design docs, use
   the term from this glossary when one exists. Do not invent a
   paraphrase.
2. If a term is missing, add it here with its defining specification
   and section, then use it.
3. Do not restate a rule as an epigram. State the rule.

---

## Lexical space, value space, lexical mapping

Defined in [XML Schema Part 2: Datatypes](https://www.w3.org/TR/xmlschema11-2/)
§2.1–§2.3.

| Term | Meaning |
|---|---|
| **value space** | The set of values a datatype denotes. |
| **lexical space** | The set of literals (character strings) that denote values of the datatype. |
| **lexical mapping** | The function from the lexical space to the value space. Generally many-to-one. |
| **canonical mapping** | A function from the value space to the lexical space, choosing one literal per value. |
| **canonical representation** | The literal the canonical mapping produces for a value. |

Consequences that matter in this codebase:

- Two literals of one datatype with different **lexical
  representations** may denote the **same value**. `"1"` and `"01"`
  are distinct in the lexical space of `xsd:integer` and map to one
  value.
- The lexical mapping is injective for some datatypes and not for
  others. `xsd:string`'s is injective, so `"colour"` and `"color"`
  denote different values.
- Distinctness of values must be decided in the **value space**.
  Deciding it in the lexical space is only correct for a datatype
  whose lexical mapping is injective.
  (`L4Factoidal.OWL.Refute.lexicalMappingIsInjective`.)
- **ill-formed literal**: a character string that is not in the
  lexical space of the datatype it is typed with. RDF 1.1 Concepts
  §5 calls the result of pairing one with that datatype an *ill-typed
  literal*.

## RDF terms

Defined in [RDF 1.1 Concepts and Abstract Syntax](https://www.w3.org/TR/rdf11-concepts/).

| Term | Meaning |
|---|---|
| **IRI** | Internationalized Resource Identifier, §3.2. |
| **literal** | Lexical form + datatype IRI, plus a language tag for `rdf:langString`, §3.3. |
| **lexical form** | The character string component of a literal, §3.3. RDF's name for a member of XSD's lexical space. |
| **blank node** | A node that is neither an IRI nor a literal, §3.4. Existentially quantified in RDF's semantics. |
| **RDF term** | An IRI, a literal or a blank node, §3.1. |
| **graph** | A set of triples, §3.1. |
| **dataset** | A default graph plus zero or more named graphs, §4. |
| **isomorphic** | Two graphs equal up to a bijection on blank nodes, §3.6. |

Language tags are compared without regard to case
([RFC 5646](https://www.rfc-editor.org/rfc/rfc5646) via RDF 1.1
Concepts §3.3), and the value space uses the lowercase form.

## RDF semantics

Defined in [RDF 1.1 Semantics](https://www.w3.org/TR/rdf11-mt/).

| Term | Meaning |
|---|---|
| **interpretation** | An assignment of denotations to IRIs and literals over a domain, §1. |
| **satisfies** | Interpretation I satisfies graph G when G is true in I, §1.3. |
| **model** | An interpretation that satisfies a graph. |
| **entails** | G entails H when every interpretation that satisfies G satisfies H, §1.4. |
| **inconsistent** | A graph with no model. |
| **entailment regime** | A named set of entailments a query answering service applies, [SPARQL 1.1 Entailment Regimes](https://www.w3.org/TR/sparql11-entailment/) §1. |
| **vacuously true** | True because the condition it quantifies over has no instances. A universally quantified statement over an empty set. |

On the last row: a statement can be vacuously true in a particular
interpretation without being entailed by a graph. `∀p.C` holds of an
individual with no `p`-successor in the interpretation being
examined; under the open world assumption another model of the same
graph may give that individual a `p`-successor outside `C`. Write
that as "true in this interpretation, not entailed by the graph".

## Open world assumption, unique name assumption

| Term | Meaning |
|---|---|
| **open world assumption** | Absence of a statement is not the negation of the statement. A graph that does not assert `x rdf:type C` does not thereby assert `x` is not a `C`. |
| **unique name assumption** | Distinct names denote distinct things. RDF and OWL do **not** make it. Two IRIs may denote one individual unless `owl:differentFrom` or a cardinality argument separates them. |

## OWL 2

Defined in [OWL 2 Structural Specification](https://www.w3.org/TR/owl2-syntax/)
and [OWL 2 Direct Semantics](https://www.w3.org/TR/owl2-direct-semantics/).

| Term | Meaning |
|---|---|
| **class expression** | A description of a set of individuals: a class name, a restriction, or a Boolean combination, Structural §8. |
| **TBox / ABox** | Terminological axioms (subclass, equivalence) / assertional axioms (class and property assertions). Description-logic terms; OWL 2 says "axiom" and "assertion". |
| **filler** | The class or datatype an object or data property restriction constrains successors to, Structural §8.2. |
| **successor** | For an individual `x` and property `p`, a `y` with `(x,y)` in the extension of `p`. |
| **CEXT(C)** | The set of individuals in the extension of class expression `C`, [OWL 2 RDF-Based Semantics](https://www.w3.org/TR/owl2-rdf-based-semantics/) §5. |
| **EXT(p)** | The set of pairs in the extension of property `p`, same section. |
| **datatype map** | The set of datatypes an OWL 2 implementation supports, plus their value spaces and lexical mappings, Structural §4. |
| **profile** | A syntactic subset of OWL 2 with better computational properties: EL, QL, RL, [OWL 2 Profiles](https://www.w3.org/TR/owl2-profiles/). |

## Tableau reasoning

Not W3C terms; standard description-logic vocabulary, used here to
describe `L4Factoidal.OWL.Refute`. Reference:
Baader, Calvanese, McGuinness, Nardi, Patel-Schneider, *The
Description Logic Handbook*, chapter 2.

| Term | Meaning |
|---|---|
| **negation normal form (NNF)** | A class expression in which negation applies only to atomic concepts. |
| **clash** | A pair of labels on one node that no interpretation can satisfy together. |
| **expansion rule** | A rule that adds labels or nodes. Deterministic rules add; non-deterministic rules branch. |
| **∃-rule / generating rule** | Creates a fresh individual to satisfy an existential restriction. |
| **≤-rule / merging rule** | Identifies two successors when a node exceeds an at-most cardinality bound. |
| **witness** | An individual created by a generating rule. |
| **blocking** | A termination condition that stops expansion when a node's labels repeat an ancestor's. Not implemented here. |
| **saturation** | Applying every deterministic rule until no rule adds anything. |

## Conformance testing

Defined in [RDF Test Suite manifests](https://www.w3.org/2001/sw/DataAccess/tests/test-manifest)
and the per-specification test READMEs.

| Term | Meaning |
|---|---|
| **manifest** | An RDF file listing test entries and their types. |
| **positive / negative syntax test** | Input must parse / must not parse. |
| **evaluation test** | Input plus expected output, compared by the specification's own equality (graph isomorphism, result-set equality). |
| **entailment test** | Premise plus conclusion; the conclusion must be entailed under the named regime. |
| **not applicable** | The implementation does not claim the feature the test exercises. Reported apart from pass and fail. |

Score reporting in this project always writes "N pass, N fail (out of
N)". A test the runner could not decide is reported in its own
column, never folded into pass or fail.

### Qualifying claims with “W3C”

“W3C” identifies a standards source or test provenance. It does not mean that
W3C has reviewed, certified, or endorsed Factoidal.

| Phrase | Required meaning |
|---|---|
| **W3C-defined semantics** | A definition is intended to model a cited W3C Recommendation or Working Draft clause. |
| **official W3C test case / corpus** | Input and expected output come from a vendored W3C test suite. If its manifest records the status, write **manifest-marked Approved** rather than the ambiguous “approved W3C test”. |
| **selected official SPARQL test cases through the persisted path** | Factoidal packed selected official fixtures into its own on-disk format and ran their original query text. This is a cross-layer regression subset, not a suite result. |
| **W3C suite result** | A manifest-driven run using the suite's comparison rules, reported with explicit pass, fail, skip/not-applicable, and unsupported counts. It is still not W3C certification. |

Do not write **W3C disk gate**. The disk formats are Factoidal/Shardborough
formats; W3C material supplies standards-derived inputs and expected results.

---

## Terms this project uses that are NOT specification terms

Listed so they are recognisable as local vocabulary.

| Local term | What it means here | Nearest specification term |
|---|---|---|
| **regime** (in `--dl`) | Which reasoning stages the OWL probe runs | entailment regime |
| **probe** | A Lean executable that runs one suite | test runner |
| **reference Lean evaluator** | The simple executable SPARQL semantics, including left-to-right BGP evaluation; it is the correctness reference for optimized paths. | SPARQL algebra evaluation |
| **optimized Lean physical-plan algorithm** | A faster Lean implementation using admitted physical structures such as predicate blocks, SRI2/OLI2 postings, and hash buckets, with refinement obligations against the reference Lean evaluator. | physical query plan |
| **pure** | Deterministic in-memory code without file I/O, Merkle admission, clocks, or harness effects. It does not distinguish Lean from another implementation language. | none |
| **scaffold blank node** | A blank node the OWL RL closure creates to support blank-node conclusion matching (`__rl_` prefix) | none |
| **witness blank node** | A blank node the materialisation pass or the refuter creates for an existential obligation (`_:bw_`, `_:tw_` prefixes) | witness |
