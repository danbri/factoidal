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
| `L4Factoidal/JSON/Value.lean` | `Parser.JSON.fst` `json_val` + accessors | `Json` (`null`/`bool`/`string`/`number`/`array`/`object`), hand-written `DecidableEq` (nested-inductive — `deriving` does not apply, see file header), `field?`/`getString?`/`getBool?`/`getArray?`/`getStringArray?` |
| `L4Factoidal/JSON/Parser.lean` | `Parser.JSON.fst` (the parser half) | `parseJson : String → Except JsonError Json`, total via fuel (mirrors the F\* fuel discipline); indexes a `List Char`, not raw bytes — see file header on why (Lean `Char` = full Unicode scalar value; sidesteps `Parser.FastString`'s byte-slicing machinery and this toolchain's `String.Pos` API) |
| `L4Factoidal/JSON/Serialize.lean` | `SPARQL.JSON.Escape.fst` (`json_escape`) + the writer shape of `Parser.JSONLD.fst`'s `jcanon_serialize` (NOT its JCS canonicalisation/field-sorting) | `Json.toString` (compact) and `Json.toStringPretty` (new; no F\* counterpart) |
| `L4Factoidal/JSON/Tests.lean` | (new) | 61 `#guard`s: RFC 8259 §13 example, every escape form, surrogate-pair decode, number-lexeme preservation, rejection cases, key-order/duplicate preservation, parse∘serialize round-trips |
| `L4Factoidal/JSON/Theorems.lean` | (new) | escape-table round-trip (exhaustive, `decide`); general literal round-trip; the STRING case general induction (`stringSegments_plain` — any length/content with no character needing escaping); a kernel-reduction finding (see file header); `RoundTripGoal` stated with the exact proof gap named (no `sorry`) |

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
- `Parser.JSON.fst`, `SPARQL.JSON.Escape.fst`: **zero** `assume val`s
  (confirmed by grep; the one hit for the string `"assume val"` in
  `SPARQL.JSON.Escape.fst` is a COMMENT referencing
  `Parser.FastString.fst`'s byte-primitive `assume val`s, not a
  declaration in either ported module). Both modules are fully defined
  and total in F\*, and the Lean port is fully defined and total too —
  no realisation gap on either side.

## A kernel-reduction finding from the JSON port (2026-08-22)

`Parser.lean`'s five mutually recursive functions
(`parseValue`/`parseObject`/`parseMembers`/`parseArray`/`parseItems`)
are `Tot`al by construction — every recursive call strictly decreases
the shared `fuel : Nat` — but Lean's equation compiler evidently
compiles this particular 5-way mutual group via WELL-FOUNDED recursion
rather than the bare structural recursion a single `fuel`-matching
function gets on its own (`stringSegments`, not part of this mutual
group, decides/`rfl`s fine in isolation). Consequence: `by decide` and
`by rfl` get "stuck" on ANY proposition mentioning `parseValue` or
anything that calls it (including `parseJson` itself) — NOT a
correctness problem (the compiled/`#eval`'d function is fine; `Tests.
lean`'s 61 `#guard`s exercise it directly), but a PROOF-TACTIC one:
kernel whnf reduction cannot unfold well-founded recursion the way it
unfolds structural recursion. Workaround, used throughout
`Theorems.lean`: `unfold parseValue parseObject ...` (equation-lemma
rewriting, which works regardless of how the recursion compiles) peels
exactly the layers a CONCRETE input needs, then `decide` closes the
remainder once no mutual-group call remains in the goal. A fully
general (∀-quantified) proof through this group needs the same
technique under an explicit induction rather than one-shot `unfold` —
see `Theorems.lean`'s `RoundTripGoal` section for exactly where this
matters (item 3, the array/object case).
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

0. JSON-LD, SPARQL Results JSON, and JSON Schema ports now unblocked
   by `L4Factoidal/JSON/` (`Parser.JSONLD.fst`/`Parser.JSONResults.fst`
   are the F\* sources; both consume `json_val`/`Json` via the same
   `field?`/`json_get_*` shape this port kept API-compatible with).
   Closing `Theorems.lean`'s `RoundTripGoal` gap (three named items:
   escaped-content strings, general number lexemes, array/object
   induction through the mutual-recursion group) is worth doing before
   or alongside the JSON-LD port, since JSON-LD's own round-trip
   proofs will need the same techniques one level up.
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
