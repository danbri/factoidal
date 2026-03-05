# Grounding Analysis: JS/HTML Demos vs. Formal Definitions

## Overview

This report analyzes how well the JavaScript demos in `docs/` are grounded
in the F\* formal specification in `formal/fstar/rdfcore11.fstar.txt`.

## Type-by-Type Mapping

| F\* Formal Definition | JS Implementation | Grounded? |
|---|---|---|
| `bnode_id = string` | `BNode` class with `.id` string | Yes |
| `wf_iri` (non-empty, contains `:`) | `Iri` class: validates non-empty + contains `:` | Yes |
| `rdf_lang_string` constant | `RDF_LANG_STRING` constant (same URI) | Yes |
| `literal {lexical_form, datatype: wf_iri, lang_tag: option string}` | `Literal {lexical, datatype: Iri, langTag}` | Yes |
| `literal_wf` biconditional (langTag ↔ rdf:langString) | Constructor throws on both violations | Yes |
| `rdf_term = T_IRI \| T_BNode \| T_Literal` | `instanceof` checks on Iri/BNode/Literal | Yes |
| `subject = S_IRI \| S_BNode` (no Literal) | `parseSubject()` only creates Iri or BNode | Yes |
| `triple = {s: subject, p: wf_iri, o: rdf_term}` | `Triple {s, p, o}` with same constraints | Yes |
| `rdf_graph = list triple` | `RdfGraph` with `triples` array | Yes |
| `empty_graph = []` | `constructor() { this.triples = []; }` | Yes |
| `graph_bnodes` (collect from s/o positions) | `bnodes()` checks s and o for BNode | Yes |

## Well-Formedness Constraints

### IRI Validation
- **F\***: `is_iri s = String.length s > 0 && has_colon s`
- **JS**: `if (!s || !s.includes(":")) throw new Error(...)`
- **Tests**: Verify rejection of empty strings and strings without colons

### Literal Well-Formedness
- **F\***: `literal_wf l = match l.lang_tag with None -> l.datatype <> rdf_lang_string | Some _ -> l.datatype = rdf_lang_string`
- **JS**: Two guard clauses in `Literal` constructor enforce both directions
- **Tests**: Verify both "lang tag with wrong datatype" and "rdf:langString without lang tag" throw

### Subject Restrictions
- **F\***: `subject = S_IRI | S_BNode` (structurally excludes Literal)
- **JS**: `parseSubject()` only produces `BNode` or `Iri`, never `Literal`

## Extensions Beyond the Formal Spec

The JS demos include features not covered by the F\* specification:

1. **Set semantics on `add()`** — deduplicates triples (F\* uses a plain list)
2. **`remove(index)`** — deletion not specified formally
3. **`findBySubject()`, `findByPredicate()`, `subjects()`** — query operations
4. **Prefix expansion/compaction** — namespace handling for the UI
5. **N-Triples and JSON serialization** — output formats
6. **`XSD_STRING` default datatype** — correct per RDF 1.1, not in F\* spec

## Minor Divergences

1. **Triple constructor doesn't enforce `p` is Iri at the type level** — relies on callers. The UI always constructs `p` as `new Iri(...)`, so this holds at runtime.
2. **Dedup semantics**: F\* `list triple` allows duplicates; JS `add()` prevents them. The JS behavior is more correct for RDF (graphs are sets).
3. **BNode collection**: F\* returns a list (may have duplicates); JS uses `Set` for uniqueness.
4. **No structural enforcement that subjects aren't Literals** — the JS `Triple` constructor accepts any object as `s`; the constraint is only at the parsing layer.

## Test Coverage

`tests.html` provides 31 test cases covering every formal constraint:
- IRI well-formedness (6 tests)
- BNode identity (4 tests)
- Literal construction and well-formedness (9 tests)
- Triple serialization (1 test)
- Graph operations including bnodes (9+ tests)
- Cross-type equality (2 tests)

## Verdict

The JS demos are **well-grounded** in the formal definitions. Every core type,
constraint, and operation in the F\* specification has a faithful counterpart in
the JavaScript implementation. Divergences are minor and generally in the
direction of being stricter (set dedup, unique bnode IDs) rather than weaker.
The test suite provides comprehensive coverage of formal constraints.
