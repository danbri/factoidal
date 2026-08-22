# L4Factoidal — F\* → Lean 4 port notes

Scope so far: the RDF term/graph data model, the SPARQL algebra core
(solution mappings, triple patterns, BGP evaluation, §18.5 operators)
and proved invariants (goal steps 1–3, 2026-08-22); then the XML layer
— the generic XML 1.0 parser and with it the well-formedness decision,
namespace processing, and a serialiser with round-trip fixtures
(2026-08-22, see "The XML stage" below).
Everything builds with `lake build` on the pinned toolchain
(`lean-toolchain`: Lean 4.33.1); the `#guard` tests in
`L4Factoidal/Tests.lean` run at build time, so a green build is also
a green test run.

## Module correspondence

| Lean 4 | Ports (F\*) | Notes |
|---|---|---|
| `L4Factoidal/RDF/Core.lean` | `RDF.Term.fsti`, `RDF.Triple.fsti` | terms, literals (incl. RDF 1.2 direction + triple terms), the three literal-equality relations, reflexivity/identity theorems |
| `L4Factoidal/RDF/XmlCanon.lean` | `RDF.Term.fsti` `xmlc_*` family | rdf:XMLLiteral exclusive-c14n value equality (WebOnt-miscellaneous-202 fix) |
| `L4Factoidal/RDF/Graph.lean` | `RDF.Graph.fsti` (+ `RDF.Dataset.Merge` renaming) | graphs as lists with set-semantics ops, datasets, blank-node renaming, membership theorems |
| `L4Factoidal/SPARQL/Algebra.lean` | `SPARQL11.Algebra.fst` Parts 1–2, §7.2–7.3/§18.5 | bindings, patterns (incl. SPARQL 1.2 triple-term patterns), `tpMatch`, `evalBgp`, join/leftJoin/union/minus/filter, `GraphPattern.eval` |
| `L4Factoidal/SPARQL/Invariants.lean` | (new; replaces the F\* SMT-`Lemma` style) | empty-pattern laws, merge/lookup characterisation, filter/minus safety, BGP monotonicity — all kernel-checked, no solver |
| `L4Factoidal/XML/Document.lean` | `Parser.XML.fst` (AST + character classes) | XML 1.0 5th ed. `[2] Char`, `[3] S`, `[4] NameStartChar`, `[4a] NameChar`, `[5] Name`; the parse tree (`Attribute`, `Node`); the prolog model (`XmlDecl` `[23]`, `Doctype` `[28]`, `Document` `[1]`); the Namespaces §3 name model (`QNameSplit`, `ExpandedName`); the convenience accessors |
| `L4Factoidal/XML/Parser.lean` | `Parser.XML.fst` (the parser) | `parseXML : String → Except XmlError Document`. In XML the parser IS the well-formedness decision; the module header lists all twenty constraints it enforces and every scope cut it inherits |
| `L4Factoidal/XML/Namespaces.lean` | `XML.Namespaces.fst` | `[7] QName` splitting, prefix-scope resolution down the tree, the default namespace, the reserved `xml`/`xmlns` prefixes and their two reserved namespace names, 1.0-vs-1.1 undeclaring, §6.3 uniqueness after expansion, undeclared-prefix rejection |
| `L4Factoidal/XML/Wellformedness.lean` | `XML.Wellformedness.fst` | `[4] NCName` (= `[5] Name` minus `:`) and the RDF/XML §7.2.4–§7.2.12 forbidden-name and conflicting-attribute checks. Despite the F\* module's name this is NOT generic XML well-formedness — see below |
| `L4Factoidal/XML/Theorems.lean` | (new) | a structural well-formedness checker over the parse tree, a serialiser, the proved tag-matching theorem, and the two general claims stated as named `Prop`s |
| `L4Factoidal/XML/Tests.lean` | (new) | 118 `#guard`s: hub post 25's two live documents, every constraint in `Parser.lean`'s header, the namespace layer, reflexivity and round-trip fixtures |
| `L4Factoidal/XML/ConfProbe.lean` | `bin/xml-runner/xml_runner.ml` (the driver only) | the `xmlconf-probe` executable: reads W3C conformance file paths from stdin, prints a well-formed/malformed verdict per file |

## Translation decisions

- **Refinements → subtypes.** `wf_iri = s:iri{is_iri s}` becomes
  `WfIri := {s : String // isIri s}`; the F\* `assert_norm` witnesses
  for constants become `rfl` proofs the kernel evaluates.
- **`literal_term_eq` collapses into `DecidableEq`.** The F\* strict
  term equality is field-by-field; in Lean that IS propositional
  equality (`Literal.termEq_iff_eq` proves the F\*
  `lemma_literal_term_eq_identity` counterpart). The COARSER engine
  equality (`Literal.eqb`: case-folded language tags, XMLLiteral
  c14n) stays a separate Bool relation, exactly as the F\* source
  warns it must.
- **Spec/engine decoupling.** The port keeps the SPECIFICATION
  evaluator: list scans, left-to-right BGP extension, nested-loop
  join. The F\* engine's index seam (`graph_store`/`RDF.Indexed`),
  selectivity planner (`choose_best_tp`), keyed hash join, fuel
  bounds, and tail-recursion (`*_tr`) rewrites are performance
  machinery over this same semantics and are deliberately not ported.
- **Filter conditions are `Binding → Bool`** at this stage; the F\*
  expression AST (`expr`, effective boolean value, all §17 builtins)
  is its own later porting stage.
- **No SMT scaffolding.** `SMTPat` hints, Z3 fuel pragmas, and
  helper lemmas whose only job was guiding the solver have no Lean
  counterpart — proofs are explicit tactic scripts. Axiom audit
  (`#print axioms`, in the build log): only `propext`,
  `Classical.choice`, `Quot.sound` — Lean's standard foundations; no
  `sorry`, no user axioms, no `native_decide`.

## The XML stage (2026-08-22)

### Bytes versus codepoints — the one structural difference

`Parser.XML.fst` indexes raw UTF-8 BYTES through `Parser.FastString`.
A large part of it exists only to cope with that: `fs_cp_at` rebuilds a
codepoint from bytes, `is_utf8_continuation_byte` keeps a byte-stepping
validator from re-probing a continuation byte, `is_valid_decoded_char`
uses the `(0xFFFD, adv = 1)` sentinel to tell "a real U+FFFD" from
"these bytes are not valid UTF-8 here", and `codepoint_to_string` is a
hand-written UTF-8 encoder for resolved character references.

**None of that has a Lean counterpart.** Lean's `String`/`Char` are
codepoint types and a `Char` is a valid Unicode scalar value by
construction (`Char.isValidChar` excludes the surrogate block), so the
invalid-UTF-8 rejection those functions perform is discharged by the
TYPE rather than by a check, and a resolved character reference is one
`Char.ofNat`. Every rule stated over codepoints is ported in full.

Two consequences worth naming:

- `XmlError.position` is a CHARACTER offset into the line-ending-
  normalised document, where the F\* reports a byte offset.
- The three W3C cases the F\* comments name as its invalid-UTF-8
  targets — `xmltest/not-wf/sa/168`, `169`, `170`, which smuggle
  surrogates and a 4-byte UCS-4 form in as well-shaped UTF-8 — are
  rejected by `xmlconf-probe` at the decode step, before the parser
  runs. Same verdict, established one layer earlier.

### `XML.Wellformedness.fst` does not hold XML well-formedness

Worth stating plainly because the module name misleads. In XML there is
no separate validator pass: a document is well-formed exactly when the
parser accepts its character string. So the generic well-formedness
constraints live in `Parser.XML.fst` itself, and the Lean port keeps
them in `XML/Parser.lean`, whose header enumerates all twenty. What
`XML.Wellformedness.fst` actually holds is `[4] NCName` (a Namespaces
production) plus the RDF/XML §7.2 name and attribute rules (an RDF/XML
concern, one layer above XML). Both are ported to
`XML/Wellformedness.lean`; the RDF/XML half has no consumer inside
`L4Factoidal.XML` and is there for completeness of the port.

### Fuel

Where the F\* writes `decreases fuel`, the Lean is structurally
recursive on a `Nat` — the same bound, checked by the same argument.
The one exception is `expandEntityValue`, which keeps the F\*'s own
lexicographic `%[depth; budget]` measure as `termination_by
(depth, budget)`: diving into a nested entity drops `depth`, scanning
forward drops `budget`. No `partial`, no `sorry`, anywhere.

### Measured against the W3C XML Conformance Test Suite

`lake exe xmlconf-probe` reads file paths on stdin and prints a verdict
per file (iron rule #6: real W3C files from disk, not fixtures).
`xmlconf-fstar-crosscheck.mjs` runs the F\*-extracted parser
(`npm/factoidal`'s `xmlWellformed`) over the same list, so the two
ports can be compared file by file rather than only by totals.

Measured 2026-08-22 on the two `xmltest` standalone collections:

| collection | Lean port | F\*-extracted parser |
|---|---|---|
| `xmltest/not-wf/sa` (186 files) | 126 rejected, 60 accepted | 123 rejected, 63 accepted |
| `xmltest/valid/sa` (120 files) | 113 accepted, 7 rejected | 110 accepted, 10 rejected |

**These are raw agreement counts, NOT a conformance score.** A `not-wf`
case this parser rejects for a different reason than the one under test
is a right verdict for the wrong reason, and the profile is XML 1.0,
non-validating, non-namespace. Both columns are subject to that caveat
equally, which is what makes the comparison between them the useful
number.

File by file, across all 306 documents the two parsers disagree on
exactly six:

- `not-wf/sa/168`, `169`, `170` — the Lean probe rejects, the
  cross-check harness reports the F\* accepting. This is an artefact of
  the HARNESS, not of the F\*: Node's `readFileSync(p, "utf8")`
  replaces the bad bytes with U+FFFD before the parser sees them.
  `Parser.XML.fst`'s own comments name these three as documents it
  rejects, so the two ports agree on the intended verdict.
- `valid/sa/023`, `085`, `086` — a genuine divergence, and the Lean
  port is right. Content that is exactly one reference to an entity
  with EMPTY replacement text (`<!ENTITY e "">` with `<doc>&e;</doc>`)
  makes the F\* `parse_xml_text` fail with "empty text node"; the
  failure is indistinguishable from "no text here",
  `parse_children` discards it, and the document is then rejected for
  want of an end tag. All three are marked VALID by the W3C suite.
  `XML/Parser.lean`'s `parseChildren` separates the two outcomes and
  accepts them, recording no `[14] CharData` node for an expansion that
  yields no characters. Pinned by `#guard` in `XML/Tests.lean`.

The remaining wrongly-accepted `not-wf` cases are shared with the F\*
and are its documented scope cut: `parse_int_subset` skips
`<!ELEMENT>`, `<!ATTLIST>`, `<!NOTATION>` and parameter-entity
declarations STRUCTURALLY (`skip_decl_to_gt`) instead of parsing their
grammar, so a malformed internal-subset declaration is stepped over
rather than rejected. Implementing the internal subset's grammar is the
obvious next rung for either tree.

### Proof status

Proved, no `sorry` and no user `axiom`:

- `Node.serialize_element_tags_match` — **WFC: Element Type Match holds
  by construction.** A `Node.element` carries ONE tag and the serialiser
  writes it into both the `[40] STag` and the `[42] ETag`, so a
  mismatched pair is unrepresentable. This is the tag-matching
  component of checker reflexivity, and it is why the checker has no
  tag-matching clause left to state.
- `Node.wellFormedList_eq_all`, `Node.wellFormed_children`,
  `Node.wellFormed_of_mem_children` — the descent into children a
  general reflexivity proof needs.
- `Node.serializeList_cons` / `_nil` — serialisation is compositional.

Stated as named `Prop` definitions, checked on fixtures by `#guard`,
NOT proved in general: `ReflexiveOnParserOutput` and
`RoundTripsOnParse`. A `def … : Prop` assumes nothing and grants no
theorem; proving either means reasoning about `parseXML`'s fuel-bounded
scans over an arbitrary input string, which is a larger piece of work
than this stage. The `#guard`s are evidence and are labelled as such.

Round-trip is `parse ∘ serialise = id` on DOCUMENTS, not
`serialise ∘ parse = id` on strings. The latter is false and should be:
`<a></a>` serialises as `<a/>`. The infoset is what the parser is a
function into.

## Assumption report — `assume val`s in the F\* originals

Requested by the port brief: unverified assumptions encountered in
the source modules.

- `Parser.XML`, `XML.Wellformedness`, `XML.Namespaces`: **zero**
  `assume val`s in all three, confirmed by `grep -c "assume val"` on
  each file (2,070 + 204 + 242 lines). The XML stack is pure F\* end to
  end — no host call-out, no I/O seam, no vendored primitive — so the
  port had nothing to dissolve by parameterisation and nothing to
  declare here. The only thing the F\* reaches outside itself for is
  `Parser.FastString`'s byte-indexed string primitives, which are
  ordinary defined functions, not assumptions.
- `RDF.Term`, `RDF.Triple`, `RDF.Graph`: **zero** `assume val`s. The
  core data model is fully defined; nothing was assumed away, and the
  port confirms it (every ported definition is total and executable).
- `SPARQL11.Algebra.fst`: **10** `assume val`s, all host-boundary
  call-outs (rule #11 of the F\* tree's own policy), none of them in
  the fragment this stage ports:
  - `string_uppercase_unicode` / `string_lowercase_unicode` —
    Unicode case mapping (host library). Lean note: `String.toLower`
    is used for language-tag folding; BCP47 tags are ASCII, so this
    is exact where the F\* tree needed the host for full Unicode.
  - `hash_md5` / `hash_sha1` / `hash_sha256` / `hash_sha384` /
    `hash_sha512` — SPARQL §17.4.4 hash builtins (vendored crypto).
  - `fx_current_datetime` — `NOW()` (clock I/O).
  - `extension_function_call` — SPARQL §17.6 extension-function host
    registry (issue #463).
  - `eval_property_path_fwd` — a forward reference into the
    property-path evaluator (an F\* module-structure artifact, not a
    semantic hole; the evaluator is defined later in the same file).
  - `service_endpoint_lookup` — SERVICE endpoint resolver (issue
    #57; the federated-query host seam).

  A Lean continuation porting the expression language will need
  positions for the first three groups (pure Lean implementations are
  feasible for all of them: Unicode tables, vendored hash cores, and
  a clock parameter instead of an ambient call).

## Next stages (in rough order of value)

1. The expression language (`expr`, EBV, §17 operators) and with it
   real `Filter`/`LeftJoin` conditions.
2. N-Triples/N-Quads parsing + serialisation (round-trip theorems —
   the F\* tree's G4/M1 program has proofs worth re-proving natively).
3. A W3C-suite harness: build a small Lean executable that reads the
   same manifests `bin/w3c-runner` does, so the Lean engine's scores
   are measured by the same files (the F\* tree's iron rule #6).
4. Wider `GraphPattern`: GRAPH, VALUES, BIND, sub-SELECT, property
   paths, and the SPARQL 1.2-track LATERAL.
5. RDFS closure + soundness — the natural first deep theorem target;
   tableau work (#448-adjacent) after that, where Lean's structural
   induction is expected to shine.
