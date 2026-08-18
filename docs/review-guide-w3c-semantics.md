# Review guide: which F\* files a W3C semantics expert should read

Written 2026-08-18 for issue
[#461](https://github.com/danbri/factoidal/issues/461) (external
review by a W3C RDF/SPARQL semantics expert). Companion documents:
[review-kernel.md](review-kernel.md) (the strongest theorem
statements, one sitting), [theorem-registry.md](theorem-registry.md)
(every proof, ~140 rows).

## The division of labor — what the expert checks that F\* cannot

The F\* verifier proves that our code satisfies **our own predicates**.
It cannot check that our predicates say what the W3C specification
says. That translation step — spec prose to F\* definition — is the
one place a mistake is invisible to the machine, and it is exactly the
expert's competence.

Concrete example: until 2026-08 (issue
[#324](https://github.com/danbri/factoidal/issues/324)), our simple
entailment engine compared literals with `literal_eq`, which folds
language-tag case. Every proof about the engine held. The engine was
still wrong, because RDF 1.1 Concepts §3.3 defines literal term
equality character-by-character, case-sensitive on the tag. F\* could
not see this; a spec reader could have, in one line.

So the review target is the **definitions**, not the proofs. Where a
file below says "check against spec section X", the question is
always: does this F\* text mean what that spec text means?

## Reading F\* without knowing F\* — the ten-minute primer

The review files use a small fragment of the language:

- `let name (x : t) : t2 = ...` — a function definition. `type t = |
  A | B of int` — a datatype with constructors (like enum cases with
  payloads). `match x with | A -> ... | B n -> ...` — case analysis.
- Refinement types: `x : nat{x < 256}` is "a natural number that is
  provably below 256". The machine rejects any code path that cannot
  prove the constraint.
- `val f ... : Lemma (requires P) (ensures Q)` — a machine-checked
  theorem: whenever P holds, Q holds. The proof body is checked by
  the verifier and then **erased at extraction** — theorems cost
  nothing at run time.
- `Tot` — the function provably terminates on all inputs. Totality is
  NOT correctness: a total function can compute the wrong answer.
- `assume val f : ...` — a trusted, unverified boundary (file I/O,
  clock, vendored crypto). Each one is either an acknowledged gap
  with an open issue, or an allowed realisation under the rule in
  [CLAUDE.md](../CLAUDE.md) iron rule #11. The current table is in
  [claude-rules/current-state.md](claude-rules/current-state.md).
- `assert_norm (...)` — asks the verifier to evaluate a closed
  expression to check a fact (used for IRI well-formedness of
  constants).
- `.fsti` vs `.fst`: an `.fsti` is the interface. In this tree
  several core modules keep **all definitions in the `.fsti`,
  written for a human reader first** (one concept per block, a prose
  definition with spec citation, then the F\* text). When both files
  exist, read the `.fsti`; the `.fst` is often only a history banner.

Executable code is **extracted** from these files to OCaml/JS — never
hand-written to "mirror" them — so the reviewed text is the shipping
logic, not documentation of it.

## The ranked list

Ranked by review value per page: declarative spec transcriptions
first (a misreading there is silent), algorithmic bulk last (there the
theorems in [review-kernel.md](review-kernel.md) do more work than
line reading).

### Tier 1 — declarative transcriptions of spec tables (audit line-by-line)

1. **`formal/fstar/RDF.Vocabulary.Axioms.fst`** (258 lines). The RDF
   and RDFS axiomatic triple tables as literal lists — one `let` per
   triple, one spec-table-row citation per `let`, written expressly
   for this audit. Check against RDF 1.1 Semantics, sections "RDF
   axiomatic triples" and "RDFS axiomatic triples"
   (https://www.w3.org/TR/rdf11-mt/). Also check the stated
   exclusion: the infinite `rdf:_n` families stay rule-generated;
   only finite tables appear here.
2. **`formal/fstar/RDFS.Closure.fsti`** (838 lines). The RDFS
   entailment rules — rdfs1, rdfs2, rdfs3, rdfs4a/4b, rdfs5, rdfs7,
   rdfs8, rdfs9, rdfs11, rdfs13, container membership, and the
   reflexivity approximation of rdfs6/rdfs10. Each rule function
   names its table row. Check the antecedent/consequent of each rule
   against the RDFS entailment rules table in RDF 1.1 Semantics.
   Known stated gaps: rdfD1 and the blank-node-minting reading of
   rdfs1 (both mint fresh bnodes; the banner explains the scoping).
3. **`formal/fstar/RDF.Term.fsti`** (573 lines). The term algebra:
   IRIs, blank nodes, literals (language tags, direction, datatypes),
   RDF 1.2 triple terms — and the **two literal-equality functions**
   (`literal_term_eq`, strict per RDF 1.1 Concepts §3.3, vs
   `literal_eq`, deliberately coarser). Check against RDF 1.1
   Concepts §3 (https://www.w3.org/TR/rdf11-concepts/). The
   equality-function split is the subject of issue
   [#324](https://github.com/danbri/factoidal/issues/324); a residual
   second path through the coarser function is documented in
   `RDF.Entailment.Simple.fst` lines 70-81 and needs an expert
   judgment on whether it matters.
4. **`formal/fstar/RDF.Graph.fsti`** (317 lines). Graphs, named
   graphs, datasets. Check against RDF 1.1 Concepts §4. Small; read
   for type-level fidelity (what CAN be a subject/predicate/object).

### Tier 2 — the entailment engines (small, dense, highest semantic risk)

5. **`formal/fstar/RDF.Entailment.Simple.fst`** (182 lines). Simple
   entailment as blank-node homomorphism, recursing into RDF 1.2
   triple terms with one shared bnode scope. Check against RDF 1.2
   Semantics, simple entailment, and the interpolation lemma of RDF
   1.1 Semantics §5. The whole engine is one page of matcher plus a
   backtracking search; the semantic content is in which equality is
   used at each position.
6. **`formal/fstar/RDF.Entailment.Regime.fst`** (271 lines). RDF /
   RDFS / D-entailment on top of the simple engine: recognized-
   datatype value equality (numeric only), triple-term opacity
   (case-sensitive language tags INSIDE triple terms), the RDF 1.2
   `rdf:reifies` range rule (`rdfs:Proposition`), owl:sameAs
   substitution. The banner states what is NOT covered (literal
   subjects, IEEE-754 value semantics, rdf:JSON canonicalization) —
   an expert should confirm the stated boundary matches the three
   remaining RDF 1.2 Semantics suite failures tracked in
   [#305](https://github.com/danbri/factoidal/issues/305).
7. **`formal/fstar/RDF.Entailment.RDFS.DatatypeClash.fst`** (280
   lines). D-entailment inconsistency: when does a graph have no
   model because a literal's lexical form is outside its recognized
   datatype's lexical space? Check against RDF 1.1 Semantics §7.
8. **`formal/fstar/XSD.Datatypes.fst`** (373 lines). The numeric
   value spaces (integer/decimal/double lexical-to-value maps) that
   D-entailment and SPARQL both consume. Check against XSD 1.1
   Datatypes lexical mappings.

### Tier 3 — large but table-driven (sample, do not read whole)

9. **`formal/fstar/OWL.Closure.fsti`** (7156 lines). The OWL 2 RL/RDF
   rules materialization, interleaved with the RDFS driver. Check a
   SAMPLE of rule functions against the OWL 2 Profiles RL rule tables
   (https://www.w3.org/TR/owl2-profiles/ §4.3). A known
   sound-but-narrow rewrite (N=1 qualified max-cardinality anchor) is
   documented in [CLAUDE.md](../CLAUDE.md) and issue
   [#236](https://github.com/danbri/factoidal/issues/236).
   `formal/fstar/OWL.RL.Refinement.fst` holds the licensing theorems
   (each rule fires only when its table row licenses it) — the
   statements, not the proofs, are the review object.
10. **`formal/fstar/RDF.Canonical.fst`** (2273 lines). RDFC-1.0
    canonicalization. Two live divergence questions between this file
    and the N-Quads serializer need spec-clause adjudication —
    language-tag lowercasing and U+FFFE/U+FFFF escaping — tracked in
    [#451](https://github.com/danbri/factoidal/issues/451). This is
    the file where an expert ruling directly unblocks queued work.
11. **`formal/fstar/SPARQL11.Algebra.fst`** (8769 lines) — do NOT
    read raw. Enter through [review-kernel.md](review-kernel.md)
    sections 2-5, which quote the strongest theorem statements
    (expression evaluation, filters, solution modifiers, results)
    with file:line anchors, then follow anchors into the file. The
    ORDER BY comparator (`sparql_order_numeric`, ~line 5172) encodes
    a WG-consensus reading (unparseable numerics sort last, then
    lexical; measured against Jena 6.2.0) that merits a spec check
    against SPARQL 1.1 Query §15.1.

## What the expert needs to know about trust boundaries

- **Proof coverage is a property of wiring, not of files.** A theorem
  about function F protects nothing if the CLI calls G. This bit us:
  issue [#443](https://github.com/danbri/factoidal/issues/443) (a
  round-trip theorem covered a serializer the shipping path did not
  call). The wiring evidence is
  [review-kernel.md](review-kernel.md) §9 (trust surface) and §10
  (how to re-check the document against the tree).
- **Test scores do not substitute for this review.** Five engine bugs
  in 2026-08 were invisible to all 1030 W3C tests and were found by
  byte-reading, differential testing against Jena, and property
  proofs. The suites check outcomes the tests happen to pin; the
  expert checks meaning.
- **`assume val` inventory**: ~87 trusted declarations remain, mostly
  storage I/O. None may carry semantics; the audit is
  [designissues/fstar-ocaml-boundary-audit.md](designissues/fstar-ocaml-boundary-audit.md).

## Questions already queued for exactly this reviewer

1. [#451](https://github.com/danbri/factoidal/issues/451) — RDFC-1.0:
   is language-tag lowercasing part of canonical N-Quads, and which
   control characters must be escaped? Two functions disagree; the
   unification is blocked on the spec ruling.
2. [#324](https://github.com/danbri/factoidal/issues/324) — the
   residual coarse-equality path when a blank node is re-seen against
   two literals differing only in tag case: does any conformant
   entailment check distinguish them?
3. [#305](https://github.com/danbri/factoidal/issues/305) — the three
   RDF 1.2 Semantics tests requiring literal/triple-term subjects:
   confirm they need a generalized-RDF term model, or find a
   conformant evasion.
4. [#236](https://github.com/danbri/factoidal/issues/236) — the OWL
   RL qualified-cardinality anchor rewrite: sound generalization to
   UNION form.
