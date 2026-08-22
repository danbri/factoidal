# L4Factoidal — F\* → Lean 4 port notes

Scope of this stage (goal steps 1–3, 2026-08-22): the RDF term/graph
data model, the SPARQL algebra core (solution mappings, triple
patterns, BGP evaluation, §18.5 operators), and proved invariants.
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

## Assumption report — `assume val`s in the F\* originals

Requested by the port brief: unverified assumptions encountered in
the source modules.

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

## Addendum (2026-08-22): N-Triples / N-Quads syntax port

Scope of this stage: RDF 1.1 N-Triples and N-Quads parsing + wire
serialisation, plus the RDF 1.2 object-position triple-term and
directional-literal extensions (W3C Working Draft, mirroring the F* tree's
`Mode_11`/`Mode_12` split). Adds `L4Factoidal/Syntax/{Lexing,NTriples,
NQuads,SyntaxTheorems}.lean` (defs/theorems) and `SyntaxTests.lean`
(46 `#guard` checks). `lake build` remains green with these five modules
wired into `L4Factoidal.lean`.

### Module correspondence

| Lean 4 | Ports (F\*) | Notes |
|---|---|---|
| `L4Factoidal/Syntax/Lexing.lean` | `Parser.NTriples.fst` character-level helpers (`hex_val_opt`, `valid_codepoint`/`safe_char_of_int`, `parse_iri_raw`/`parse_iri_body_acc`, `parse_string_literal`/`parse_string_body`, `parse_lang_tag`, `parse_lang_dir_12`, `parse_bnode`, `pws`/`skip_comment`/`skip_eol`) | codepoint-level (`List Char`) instead of the F* source's byte-level (`Parser.FastString`) primitives — see Assumption report below. Structural recursion throughout; no fuel needed (Lean's nested cons-pattern recursion decreases automatically where the F* source needed `decreases fuel`). |
| `L4Factoidal/Syntax/NTriples.lean` | `Parser.NTriples.fst` triple-level grammar (`parse_subject`/`parse_object`/`parse_object_12_f`/`parse_triple`/`parse_triple_12`/`parse_ntriples_strict`/`parse_ntriples_strict_12`) + the N-Triples half of `RDF.NQuads.Serialize.fst` (`nq_term_to_string`, `nq_subject_to_string`, `nq_line_for_triple_default_graph`) | `Mode` (`rdf11`/`rdf12`) is the Lean counterpart of `rdf_syntax_mode`. Only the STRICT parse entry points are ported (see "Deliberately not ported" below). `readObject12`'s triple-term nesting uses an explicit `fuel : Nat` — the one place this port keeps the F* source's fuel style, because the recursive call is reached after parsing a subject/predicate in between (not a direct cons-pattern suffix), so plain structural recursion on the char list is unavailable there. |
| `L4Factoidal/Syntax/NQuads.lean` | `Parser.NQuads.fst` (`parse_graph_label`/`parse_opt_graph_label`/`parse_nquad`/`parse_nquad_12`/`parse_nquads_strict`/`parse_nquads_strict_12`/`dataset_add_quad`) + the N-Quads half of `RDF.NQuads.Serialize.fst` (`nq_line_for_triple`) | Reuses `Syntax.NTriples`'s subject/predicate/object readers verbatim, matching the F* source's own module structure (`Parser.NQuads.fst` `open`s `Parser.NTriples`). `addQuad` is a direct-append version of `dataset_add_quad`; the F* source's `graph_add_unchecked` + `dataset_finalise` prepend-then-reverse split is a performance pragmatic over the identical set semantics, not ported (see below). |
| `L4Factoidal/Syntax/SyntaxTheorems.lean` | (new; no direct F* counterpart — the F* tree's G4/M1 round-trip program is SMT-`Lemma`-based) | ECHAR/UCHAR decode round-trip facts on concrete escape-table entries (`rfl`-proved); the general graph round-trip theorem's BASE CASE (`graph_roundtrip_nil`, proved); the general theorem's FULL statement + induction skeleton (commented out, not `sorry` — see the file's module header for the two blocking gaps). |
| `L4Factoidal/Syntax/SyntaxTests.lean` | (new; hand-written fixtures in the style of `third_party/testing/w3c/rdf/rdf11/rdf-n-triples/` — that submodule is absent in this worktree, see below) | 46 `#guard`s: positive/negative RDF 1.1 N-Triples, RDF 1.2 fixtures (directional literals, triple terms, nested triple terms, legacy `<< >>` rejection), serialise-then-parse round trips on every positive fixture graph, N-Quads with two named graphs + a blank-node graph label + a rejected literal graph label. |

### Deliberately NOT ported (spec/pragmatics split, matching the existing
`RDF.Graph`/`SPARQL.Algebra` convention in this tree)

- The F* source's FAST-PATH / SLOW-PATH split (`scan_iri_end` vs.
  `parse_iri_body_acc`, `scan_string_fast` vs. `parse_string_body`) — a
  byte-buffer performance optimisation; this port has one code path per
  reader.
- The LENIENT document parsers (`parse_ntriples`/`parse_ntriples_12`/
  `parse_nquads`/`parse_nquads_12` — skip a malformed line and keep
  going) and the streaming/count/validate-only variants (`fold_ntriples`,
  `fold_nquads`, `count_ntriples`, `count_nquads_quads`, every
  `validate_*` function, `parse_nquads_flat`). All are CLI/import-
  pipeline/performance pragmatics over the identical grammar the STRICT
  entry points this port ships already specify; this matches the
  existing `L4Factoidal` convention of porting the SPECIFICATION
  evaluator, not the OCaml extraction's performance seam.
- RDF 1.2's inline-whitespace relaxation between a closing quote and a
  following `@lang`/`^^datatype` (F* `parse_literal_12`'s `pws`-then-peek
  logic, exercised by the W3C c14n suite's `extra_whitespace-03`/`-04`
  tests). Not exercised by anything in `SyntaxTests.lean`; flagged as a
  known gap rather than silently dropped.
- The F* source's CANONICAL N-Triples/N-Quads serialiser
  (`nq_canon_term`/`canonical_nt_document`/`canonical_nq_document` —
  uppercase `\u00XX` for every C0/DEL byte, lowercased language tags,
  U+FFFE/U+FFFF escaping) — a distinct rendering contract for the
  RDFC-1.0 c14n test suite, not the general wire serialiser
  `Graph.toNTriples`/`Dataset.toNQuads` port.

### Assumption report — F\* primitives this port replaces or cannot carry over

- `Parser.FastString`'s byte-indexed primitives (`fs_byte_length`,
  `fs_byte_index`, `fs_byte_at`, `fs_byte_sub`, `fs_cp_at`,
  `fs_utf8_of_codepoint`, `unsafe_char_of_d7ff`) — all `assume val`
  realisations in the F* tree (rule #11(b), pure host-string-library
  call-outs; the F* source's own comments cite issue #70 and #325 for
  why the byte/codepoint split exists and a bug it once caused). This
  port needs NONE of them: Lean's `List Char` is already
  codepoint-indexed (produced by `String.toList`, which decodes UTF-8),
  so every byte-vs-codepoint distinction the F* source's comments walk
  through (the `#325` double-encoding bug, the ASCII-fast-path vs.
  codepoint-slow-path split in `is_bnode_char_cp`) collapses to a single
  codepoint-level definition with no host primitive at all. This is a
  case where the Lean port is STRUCTURALLY simpler than the F* source,
  not merely a different implementation of the same primitive.
- `RDF.Term.fsti`'s `is_iri` (ported as `RDF.Core.isIri`, already noted
  zero-`assume val` in the original port) is reused unchanged by this
  stage's `mkIri`. Its coarseness (non-empty + contains `:`, not the
  full IRIREF-forbidden-codepoint grammar) is the SAME gap the F* source
  has — see `SyntaxTheorems.lean`'s GAP #1 note. Not a regression this
  port introduced; recorded here because it is the reason the general
  round-trip theorem could not be closed in this session.
- No new `assume val`-equivalent (`axiom`/`opaque`/`partial`) was
  introduced anywhere in `Syntax.*`. Every reader is a total Lean
  function (`#print axioms` on the proved theorems in
  `SyntaxTheorems.lean` shows only `propext`/`Classical.choice`/
  `Quot.sound` — Lean's standard foundations, the same baseline
  `L4Factoidal.Tests`'s own audit lines already carry).

### Deviation from the port brief's literal signature order

The brief specified `parseNTriples (mode := .rdf11) (s : String)` /
`parseNQuads (mode := .rdf11) (s : String)` (default parameter FIRST).
Lean 4 does not skip a leading `optParam` in a bare positional call —
`parseNTriples "text"` with `mode` first is a TYPE ERROR (confirmed by a
scratch test: `f "hello"` against `f (mode : M := .a) (s : String)`
rejects `"hello"` against the `Mode`-typed first slot rather than
skipping to `s`). This port therefore declares the STRING parameter
first and `mode` second, trailing, with the default:
`parseNTriples (s : String) (mode : Mode := .rdf11)`. Same reordering
for `Graph.toNTriples`/`Dataset.toNQuads` (`g`/`ds` first, `mode`
second). Every call site in `SyntaxTests.lean`/`SyntaxTheorems.lean`
uses this order; `parseNTriples s` (RDF 1.1 default) and
`parseNTriples s .rdf12` both work as intended.

### Core/Graph change that would help (not made — brief scopes this port
to new files only)

`RDF.Graph.lean`'s `NamedGraph` derives `Repr` only, not `DecidableEq`
(`Dataset` likewise). This port's tests need to compare `List NamedGraph`
for the N-Quads round-trip check and cannot add `deriving DecidableEq`
without editing `RDF.Graph.lean`, so `SyntaxTests.lean` carries a local
`namedGraphsEq`/`namedGraphEq` helper instead (pointwise `name`/`graph`
comparison, `List Triple`'s own derived `DecidableEq` doing the real
work). Adding `deriving DecidableEq` to `NamedGraph` and `Dataset` in
`RDF.Graph.lean` would let that helper be replaced by ordinary `==`,
matching the `instBEqOfDecidableEq` convention this project's own
pitfall list (`skills/factoidal-lean-basics`) already recommends for
every other structure in the tree.
