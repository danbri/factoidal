# WebOnt-imports-011 diagnosis (2026-04-25)

**Agent Heth — diagnosis only.** Triage memo (`2026-04-24-owl-rl-posent-triage.md`,
case #24) flagged this as *"smells like an `xml:base=""` bnode-vs-IRI artefact in
`Parser.RDFXML`, not closure"*. After tracing the test, the diagnosis is
**different**: the parser is correct; the test is genuinely out-of-scope for
the current OWL-RL closure runner because it requires `owl:imports` resolution
(loading the imported ontology from the catalog), which the runner does not do.

## The test

From `third_party/testing/owl/profile-RL.rdf`, identifier `WebOnt-imports-011`:

**Premise** (xml:base = `…/imports/premises011`):

```xml
<owl:Ontology rdf:about=''>
    <owl:imports rdf:resource="http://www.w3.org/2002/03owlt/imports/support011-A"/>
</owl:Ontology>
<ont:Man rdf:about='http://example.org/data#Socrates'/>
```
where `xmlns:ont='http://www.w3.org/2002/03owlt/imports/support011-A#'`.

**Conclusion** (xml:base = `…/imports/conclusions011`):

```xml
<owl:Ontology/>
<rdf:Description rdf:about='http://example.org/data#Socrates'>
    <rdf:type><owl:Class rdf:about='support011-A#Mortal'/></rdf:type>
</rdf:Description>
```

**Imported support011-A** (xml:base = `…/imports/support011-A`):

```xml
<owl:Ontology rdf:about=''/>
<owl:Class rdf:ID='Man'><rdfs:subClassOf rdf:resource='#Mortal'/></owl:Class>
<owl:Class rdf:ID='Mortal'/>
```

The catalog also contains a sibling `<owl:Thing>` carrying
`test:rdfXmlInputOntology` for support011-A, linked to the test case via
`test:importedOntology`.

## What the runner currently does

`formal/fstar/ocaml-output/owl_runner.ml` line 351:

```ocaml
let closure = owl_rl_closure_with_reflexivity g_p fuel_100 in
```

`g_p` is just the parsed premise. The runner never reads
`test:importedOntology` and never inlines the imported triples. So the closure
sees only:

- `<premises011> rdf:type owl:Ontology`
- `<premises011> owl:imports <support011-A>`
- `<Socrates> rdf:type <support011-A#Man>`

…plus RDFS/OWL-RL closure (which, lacking the `Man rdfs:subClassOf Mortal`
axiom from support011-A, cannot derive `<Socrates> rdf:type <Mortal>`).

## What the conclusion expects

After parsing, the conclusion graph is:

1. `_:rdfxml_b0 rdf:type owl:Ontology` — the `<owl:Ontology/>` element has no
   `rdf:about`/`rdf:ID`, so per RDF/XML §6.1.4 it is a fresh blank node. This
   is the parser doing the spec-correct thing, **not** an `xml:base`
   regression.
2. `<Socrates> rdf:type <…/imports/support011-A#Mortal>`.

The runner reports the first missing triple (#1 above):

```
FAIL  WebOnt-imports-011
    missing conclusion triple: _:rdfxml_b0 <…#type> <…owl#Ontology>
```

But triple #2 is also missing, and is the substantive entailment claim.

## Why Zeta's parser hypothesis doesn't hold

The triage memo guessed an `xml:base=""` bnode-vs-IRI mismatch. There is no
`xml:base=""` anywhere in this test — both premise and conclusion declare
non-empty `xml:base` values. The bnode-vs-IRI difference between `<owl:Ontology
rdf:about=''>` (premise → IRI = base) and `<owl:Ontology/>` (conclusion →
fresh bnode) is correct per RDF/XML §6:

- §6.1.4 *node element production*: a node element with no `rdf:about`,
  `rdf:ID`, or `rdf:nodeID` produces a blank-node subject.
- §5.4 *resolving relative URIs*: an empty IRI reference resolves to the base
  IRI itself.

`Parser.RDFXML.fst` implements both correctly:

- `resolve_iri` (line 190): `String.length rel = 0 → base`.
- `determine_subject` (line 575): `find_attr "rdf:about" = None` and
  `rdf:ID = None` and `rdf:nodeID = None` → `fresh_bnode`.

A "fix" that made `<owl:Ontology/>` resolve to the base IRI would be
**wrong** — it would break every other test that relies on §6.1.4 fresh-bnode
semantics, and would not actually solve this test (triple #2 still requires
owl:imports loading).

## What would actually fix the test

Two layered changes, neither parser-side:

1. **Runner: load `test:importedOntology` content into the premise graph.**
   The catalog has, for each `test:TestCase`, a sibling `<owl:Thing
   rdf:about="…">` carrying `test:rdfXmlInputOntology` (a literal of the
   imported document) and `test:importedOntologyIRI`. The runner already walks
   the catalog and hashes per-subject info; it would extend `test_case_info`
   with `imports : (iri * literal) list` and, when running positive
   entailment, parse each imported document and append its triples to `g_p`
   before closure.
   - Estimated change: ~40 lines OCaml in `owl_runner.ml`, no new F\*.
   - Risk: this is **runner harness logic**, not RDF/SPARQL semantics, so
     CLAUDE.md rule #15 permits it. owl:imports *resolution* (i.e. dereferencing
     URLs) is genuinely out of scope; loading from the catalog's
     `test:rdfXmlInputOntology` literal is just I/O glue.

2. **Bnode-match relaxation for "anonymous owl:Ontology header" triples.**
   Even after #1 produces `<premises011> rdf:type owl:Ontology` in the
   closure, the conclusion triple `_:rdfxml_b0 rdf:type owl:Ontology` only
   matches structurally if the closure has a *bnode* with type Ontology. The
   premise's ontology header is named (`<premises011>`), the conclusion's is
   anonymous. The OWL test convention seems to treat anonymous Ontology
   headers as existential ("there exists *some* Ontology"). Either:
   - Skip the anonymous-Ontology-header triple in the conclusion (it's a
     ceremonial header, not an entailment claim), or
   - Generalise structural bnode-match: a bnode pattern matches *any* term
     at that position, not just bnodes. The runner already notes the match is
     "structural only; full isomorphism deferred"; this just relaxes one more
     direction.
   - Estimated change: ~10 lines OCaml.

Combined, the test would flip 13/30 → 14/30 (and possibly unblock other
imports-family tests, though imports-011 is the only one currently in
profile-RL PositiveEntailment).

## Recommendation

**Do not edit `Parser.RDFXML.fst` for this test.** The parser is correct.
File a separate ticket for *runner* enhancement (load `test:importedOntology`
+ generalised bnode match), or treat WebOnt-imports-011 as out-of-scope for
pure closure work and reclassify it under Zeta's mode (f) — out-of-scope.

The parser-side concern from the triage memo is a false alarm. No `.fst`
edit, no F\* re-verification, no extraction needed.

## Files touched

- (this doc only)
