# 2026-07-03 — OWL-RL profile PE failures: per-test root causes + fix sketches

**Status:** diagnosis + fix sketches only — no code changed. Follows up
the "Split the 10 failing PE tests off #262" item in
[`2026-07-03-owl-rl-sameas-blowup-diagnosis.md`](2026-07-03-owl-rl-sameas-blowup-diagnosis.md)
§6. Measurements taken with the committed `bin/linux-x86_64/owl_runner`
(`timeout 600 ./bin/linux-x86_64/owl_runner -v third_party/testing/owl/profile-RL.rdf`).
All file references are to
[`formal/fstar/RDF.Graph.Executable.fst`](../../formal/fstar/RDF.Graph.Executable.fst)
unless stated otherwise.

## 1. Verified baseline

Full catalog, verbose run, from the repo root: the PE section scores
**20 pass, 10 fail (out of 30) in 11.77 s**, matching the diagnosis doc
and `docs/test-results/latest.json`. No `[owl_closure_timeout]` fired
in the PE section (the two 30 s cap trips are in the 76-test
ConsistencyTest section, as before). The `-v` flag prints the first
missing conclusion triple per failing test; those are quoted verbatim
per test below.

Two harness facts shape every diagnosis (both from
[`bin/owl-runner/owl_runner.ml`](../../bin/owl-runner/owl_runner.ml)
lines 329–367):

1. **The bnode matcher is fully existential per position.** A bnode in
   a conclusion-triple position matches *any* term at that position in
   the closure. So a reported miss on a bnode-containing pattern means
   the closure has **no triple at all** with that predicate and the
   remaining exact positions. The lenient-bnode caveat therefore cuts
   *for* us here: none of the 7 bnode-shaped failures is a matcher
   limitation — each one is a genuinely absent predicate/object
   combination. Conversely, it means the fixes below only have to
   materialise *one witness structure*, not an isomorphic copy of the
   conclusion graph.
2. **Group E axioms type every mentioned IRI `owl:Thing`**
   (`owl_thing_axioms`, line 3818), so conclusion patterns like
   `<Stewie> rdf:type _:b` are already satisfied; only the
   class-expression scaffold triples are missing.

## 2. Per-test breakdown

### 2.1 DisjointClasses-001 — missing `owl:complementOf` scaffold

- **Missing conclusion triple (first miss, `-v`):**
  `_:rdfxml_b1 <owl:complementOf> <http://example.org/Girl>`
- **Premise:** `Boy owl:disjointWith Girl`; `Stewie rdf:type Boy`.
  **Conclusion:** `Stewie rdf:type [ owl:Class ; owl:complementOf Girl ]`.
- **Root cause: missing rule.** No closure rule ever *emits*
  `owl:complementOf` (grep confirms: `owl_complementOf_iri` is only
  consumed, in `owl_rule_disjoint_with_propagation` at 2259, which
  deliberately notes "we do NOT emit complementOf from disjointWith —
  that direction is unsound"). That note is right for the *class-level*
  triple `Boy owl:complementOf Girl` (complement is strictly stronger
  than disjointness). It does not apply to the *existential* reading
  the test wants: `disjointWith(c1,c2)` entails every c1-instance is in
  the class `complementOf(c2)` — a bnode class expression, sound under
  the RDF-based semantics because bnodes are existentials, exactly the
  reading the runner's matcher already implements.
- **Not in the RL rule table.** OWL 2 RL Table 4 has only cax-dw (the
  inconsistency direction). Deriving a bnode-structured conclusion is
  outside Theorem PR1's completeness guarantee (the theorem requires a
  bnode-free conclusion), so this is a sound *extension*, in the same
  family as the existing `owl_rule_svf2_existential_witness` /
  `cls-maxqc1` canonical-bnode materialisations. Deterministic
  `__rl_`-prefixed skolem bnodes keep it idempotent and keep
  `edge_subject_is_safe` (2482) filtering it out of the
  canonical-generating rules.

**Fix sketch** (new rule, shape of `owl_rule_disjoint_with_propagation`;
slot immediately after `g3_disj` in `owl_rl_closure_step`):

```fstar
// Canonical complement-class bnode, one per named class.
let canonical_complement_bnode (c : wf_iri) : bnode_id =
  String.concat "" ["__rl_comp__"; c]

// cax-dw-comp (sound extension, not in RL Table 4): from
// (c1 owl:disjointWith c2) every c1-instance lies outside c2, i.e.
// inside the class expression complementOf(c2). Materialise that
// expression as a deterministic skolem bnode plus memberships.
// IRI-IRI guard per the bnode-pollution rule (parent9 lesson).
let owl_rule_disjoint_to_complement (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_disjointWith_iri then
        match t.s, t.o with
        | S_IRI c1, T_IRI c2 ->
          if c2 = owl_Thing || c2 = owl_Nothing then acc
          else
            let cb : subject = S_BNode (canonical_complement_bnode c2) in
            let shape1 : triple = { s = cb; p = owl_complementOf_iri; o = T_IRI c2 } in
            let shape2 : triple = { s = cb; p = rdf_type; o = T_IRI owl_Class } in
            let acc1 = add_triple_unchecked (add_triple_unchecked acc shape1) shape2 in
            let members = find_subjects_indexed ig rdf_type (T_IRI c1) in
            List.Tot.fold_left
              (fun (acc2 : rdf_graph) (x : subject) ->
                let memb : triple =
                  { s = x; p = rdf_type; o = T_BNode (canonical_complement_bnode c2) } in
                add_triple_unchecked acc2 memb)
              acc1 members
        | _, _ -> acc
      else acc)
    g g
```

- **Risk: low-medium.** Adds ≤ 2 + |instances(c1)| triples per
  disjointWith pair; `disjoint_with_propagation` symmetry doubles the
  pairs. The `__rl_comp__` bnodes are excluded from
  `cls-maxqc1`/`svf2`/`exactqc1` by the existing `bnode_is_rl_canonical`
  check inside `edge_subject_is_safe`. Watch the NegativeEntailmentTest
  section (currently 3 pass, 3 fail of 6): any NE non-conclusion that
  mentions complementOf could flip. Watch entailment-regime 70/70 for
  bnode leakage into `?class` bindings (the guards should hold; the
  parent9 pattern is the precedent).

### 2.2 DisjointClasses-003 — 2.1 plus missing AllDisjointClasses expansion

- **Missing conclusion triple:** same shape as 2.1
  (`_:rdfxml_b1 <owl:complementOf> <http://example.org/Girl>`, then
  `...Dog` behind it).
- **Premise:** `owl:AllDisjointClasses` node with
  `owl:members (Boy Girl Dog)`; `Stewie rdf:type Boy`.
  **Conclusion:** `Stewie` typed `complementOf(Girl)` and
  `complementOf(Dog)`.
- **Root cause: two missing rules.** (a) Nothing expands
  `owl:AllDisjointClasses` + `owl:members` into pairwise
  `owl:disjointWith` (grep: no rule mentions AllDisjointClasses or
  reads `owl:members` — the only `owl:members` reference is the
  schema-metapredicate guard at 2203). RL's cax-adc consumes the list
  in-place for the inconsistency check; we need the materialised
  pairwise form so 2.1's rule (and `is_inconsistent`'s disjoint-class
  scan, and the tableau bridge) can fire. (b) Rule 2.1.

**Fix sketch** (reuses `decode_chain_list` at 3109, the IRI-list walker
already used by prp-spo2; slot before `owl_rule_disjoint_with_propagation`
so symmetry + 2.1 see the pairs in the same step):

```fstar
// cax-adc-expand: (x rdf:type owl:AllDisjointClasses) with
// (x owl:members L), L an all-IRI rdf list (c1 ... cn), implies
// pairwise (ci owl:disjointWith cj) for i distinct from j. Bnode
// class expressions in L make decode_chain_list return None (guard).
let owl_rule_all_disjoint_classes (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdf_type && rdf_term_eq t.o (T_IRI owl_AllDisjointClasses_iri) then
        List.Tot.fold_left
          (fun (acc1 : rdf_graph) (l_term : rdf_term) ->
            match term_to_subject l_term with
            | None -> acc1
            | Some l_subj ->
              (match decode_chain_list g ig l_subj with
               | Some cs ->
                 List.Tot.fold_left (fun (acc2 : rdf_graph) (c1 : wf_iri) ->
                   List.Tot.fold_left (fun (acc3 : rdf_graph) (c2 : wf_iri) ->
                     if c1 = c2 then acc3
                     else add_triple_unchecked acc3
                            ({ s = S_IRI c1; p = owl_disjointWith_iri; o = T_IRI c2 }))
                     acc2 cs)
                   acc1 cs
               | None -> acc1))
          acc (find_objects_indexed ig t.s owl_members_iri)
      else acc)
    g g
```

New IRI constants needed: `owl_AllDisjointClasses_iri`,
`owl_members_iri` (assert_norm pattern as at 1376).

- **Risk: low.** n² pairwise triples per AllDisjointClasses axiom;
  the pairs feed `is_inconsistent`'s disjointness scan, so previously
  blind ConsistencyTests with AllDisjointClasses premises may start
  detecting real inconsistencies — a *newly honest* delta to expect in
  the Cons/Inc sections (currently 75 pass, 1 fail of 76; 4 pass, 10
  fail of 14).

### 2.3 New-Feature-DisjointDataProperties-002 / New-Feature-DisjointObjectProperties-002 — missing `owl:AllDifferent` materialisation

- **Missing conclusion triple (both):**
  `_:rdfxml_b1 <rdf:type> <owl:AllDifferent>` — no AllDifferent-typed
  node exists anywhere in either closure.
- **Premises:** `owl:AllDisjointProperties` over three properties, plus
  three assertions. Object variant: all three edges share subject
  `Stewie` (`hasFather Peter`, `hasMother Lois`, `hasChild StewieJr`).
  Data variant: three *different* subjects sharing the literal value
  `"Peter Griffin"` (`Peter hasName`, `Peter_Griffin hasAddress`,
  `Petre hasZip`). **Conclusions:** `owl:AllDifferent` node with
  `owl:members` listing the three individuals.
- **Root cause: three missing rules** (matcher is fine — with pairwise
  `differentFrom`-backed AllDifferent structures materialised, every
  conclusion triple matches, including the exact-object
  `_:l rdf:first <Peter>` cells; verified by hand against the matcher
  semantics in §1):
  1. No `owl:AllDisjointProperties` → pairwise
     `owl:propertyDisjointWith` expansion (same gap as 2.2a; the
     existing contrapositive `owl_rule_pdw_to_differentFrom` at 1904
     never fires because the pairwise triples are absent).
  2. The existing contrapositive covers only the **shared-subject**
     shape (`s p1 o1`, `s p2 o2` → `o1 differentFrom o2`) — that plus
     rule 1 is sufficient for the *object*-property variant. The
     *data*-property variant needs the **shared-value** contrapositive:
     `x p1 v`, `y p2 v` → `x differentFrom y` (v may be a literal; if
     x = y the pair (x, v) would inhabit two disjoint properties —
     prp-pdw). Not currently implemented.
  3. Nothing rewrites derived `owl:differentFrom` pairs into the
     `owl:AllDifferent` + `owl:members` surface form the conclusions
     use. A pairwise AllDifferent node per differentFrom pair is
     semantically exact (Table 5 mapping of a 2-member
     DifferentIndividuals axiom) and satisfies the 3-member conclusion
     under the existential matcher.

**Fix sketch — rule 1** mirrors 2.2's expansion with
`owl_AllDisjointProperties_iri` / `owl_propertyDisjointWith` in place
of the class vocabulary (same list decode, same guards; slot next to
2.2's rule). **Rule 2:**

```fstar
// prp-pdw-shared-value contrapositive: disjoint p1/p2 cannot share a
// (subject, value) pair, so subjects reaching the same value through
// p1 and p2 are distinct individuals. Values compared by rdf_term_eq
// so literals (data properties) work; find_subjects_indexed does the
// object-side lookup against the step snapshot.
let owl_rule_pdw_shared_value_to_differentFrom (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  let pdw_pairs = (* same harvest as owl_rule_pdw_to_differentFrom, 1905-1915 *) ... in
  List.Tot.fold_left
    (fun (acc : rdf_graph) (pair : (wf_iri & wf_iri)) ->
      let (p1, p2) = pair in
      List.Tot.fold_left
        (fun (acc1 : rdf_graph) (t1 : triple) ->
          if t1.p = p1 then
            let ys = find_subjects_indexed ig p2 t1.o in
            List.Tot.fold_left
              (fun (acc2 : rdf_graph) (y : subject) ->
                if subject_eq y t1.s then acc2
                else add_triple_unchecked acc2
                       ({ s = t1.s; p = owl_differentFrom; o = subject_to_term y }))
              acc1 ys
          else acc1)
        acc g)
    g pdw_pairs
```

(The `...` harvest is the verbatim fold at 1905–1915; not repeated.)
**Rule 3:**

```fstar
let canonical_adf_bnode  (k1 k2 : string) : bnode_id =
  String.concat "" ["__rl_adf__";  k1; "__vs__"; k2]
let canonical_adfl1_bnode (k1 k2 : string) : bnode_id =
  String.concat "" ["__rl_adfl1__"; k1; "__vs__"; k2]
let canonical_adfl2_bnode (k1 k2 : string) : bnode_id =
  String.concat "" ["__rl_adfl2__"; k1; "__vs__"; k2]

// eq-diff-adf: surface every differentFrom pair as its Table 5
// AllDifferent form. One unordered pair emits once (key order picks
// the representative; differentFrom symmetry at 1688 supplies the
// mirror pair, which the key guard then skips). __rl_ prefix keeps
// the list bnodes out of cls-maxqc1 / svf2 via edge_subject_is_safe.
let owl_rule_differentFrom_to_allDifferent (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_differentFrom then
        match term_to_subject t.o with
        | None -> acc
        | Some y ->
          let k1 = subject_to_key t.s in
          let k2 = subject_to_key y in
          if string_key_le k2 k1 then acc   // one emission per unordered pair
          else
            let adf : subject = S_BNode (canonical_adf_bnode k1 k2) in
            let l1 = canonical_adfl1_bnode k1 k2 in
            let l2 = canonical_adfl2_bnode k1 k2 in
            add_triples_if_new acc [
              { s = adf;        p = rdf_type;       o = T_IRI owl_AllDifferent_iri };
              { s = adf;        p = owl_members_iri; o = T_BNode l1 };
              { s = S_BNode l1; p = rdf_first;       o = subject_to_term t.s };
              { s = S_BNode l1; p = rdf_rest;        o = T_BNode l2 };
              { s = S_BNode l2; p = rdf_first;       o = subject_to_term y };
              { s = S_BNode l2; p = rdf_rest;        o = T_IRI rdf_nil_iri } ]
      else acc)
    g g
```

`string_key_le` is a total string order on subject keys — reuse the
comparator that backs `graph_dedup_sort` rather than adding a new one.
New constant: `owl_AllDifferent_iri`.

- **Risk: medium — this is the one to watch for #262 interaction.**
  Six triples per unordered differentFrom pair, and differentFrom pair
  counts are quadratic in contrapositive-heavy graphs. `add_triples_if_new`
  bounds re-emission, and the emission itself never feeds further rules
  (the `__rl_` guard), but per-step scan cost grows with the pair
  count. If the ConsistencyTest section's two 30 s cap trips worsen,
  gate this rule on pairs whose subjects are named individuals, or land
  it after the #262 snapshot-cluster fix. Also re-check the NE section:
  more surface triples can only flip NE tests toward
  FAIL/unexpected-entailment; none of the 6 NE non-conclusions mentions
  AllDifferent (checked in the catalog), so the expected delta is zero.

### 2.4 New-Feature-ObjectQCR-002 — missing max-1-qualified contrapositive

- **Missing conclusion triple:**
  `_:rdfxml_b1 <owl:complementOf> <http://example.org/Woman>`
- **Premise:** `Peter rdf:type [ owl:Restriction ; owl:onProperty
  fatherOf ; owl:maxQualifiedCardinality "1"^^xsd:nonNegativeInteger ;
  owl:onClass Woman ]`; `Peter fatherOf Stewie, Meg`; `Meg rdf:type
  Woman`; `Stewie owl:differentFrom Meg`. **Conclusion:** `Stewie
  rdf:type [ owl:Class ; owl:complementOf Woman ]`.
- **Root cause: missing rule.** The max-side rules
  (`owl_rule_cls_maxqc1` at 2691, `owl_rule_cls_maxc2` at 2804) cover
  canonical-membership and the sameAs-merging direction
  (cls-maxqc4-style). The needed inference is the *contrapositive*:
  Meg fills the single Woman slot, Stewie is different from Meg, hence
  Stewie is not a Woman — membership in `complementOf(Woman)`. No RL
  table rule produces it (bnode conclusion again, outside PR1); it is a
  sound Horn specialisation in the same family as the existing
  fp/ifp/pdw contrapositives (1947–2016).

**Fix sketch** (slot next to `owl_rule_cls_maxqc1`, i.e. after the
sameAs/differentFrom cluster; shares `canonical_complement_bnode` from
2.1):

```fstar
// cls-maxqc-comp: data-side restriction _:r with
//   (_:r owl:maxQualifiedCardinality "1"^^xsd:nonNegativeInteger)
//   (_:r owl:onProperty P) (_:r owl:onClass C), C a named class,
// plus (x rdf:type _:r), (x P y1), (y1 rdf:type C), (x P y2),
// (y1 owl:differentFrom y2): the single C-slot is taken by y1, so
// y2 lies outside C — emit the complementOf(C) scaffold + membership.
let owl_rule_cls_maxqc_comp (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = owl_maxQualifiedCardinality_iri
         && rdf_term_eq t.o (T_Literal one_nonNegInteger_literal) then
        match find_objects_indexed ig t.s owl_onProperty_iri,
              find_objects_indexed ig t.s owl_onClass_iri with
        | (T_IRI p) :: _, (T_IRI c) :: _ ->
          let xs = find_subjects_indexed ig rdf_type (subject_to_term t.s) in
          List.Tot.fold_left
            (fun (acc1 : rdf_graph) (x : subject) ->
              let ys = find_objects_indexed ig x p in
              List.Tot.fold_left
                (fun (acc2 : rdf_graph) (y1 : rdf_term) ->
                  if term_has_type ig y1 c then
                    List.Tot.fold_left
                      (fun (acc3 : rdf_graph) (y2 : rdf_term) ->
                        if differentFrom_in_graph g y1 y2 then
                          emit_complement_membership acc3 c y2   // scaffold + (y2 rdf:type __rl_comp__C)
                        else acc3)
                      acc2 ys
                  else acc2)
                acc1 ys)
            acc xs
        | _, _ -> acc
      else acc)
    g g
```

`term_has_type` / `emit_complement_membership` are small helpers
(5 lines each) factored from 2.1; `differentFrom_in_graph` exists
(used at 1971).

- **Risk: low.** Guarded by the exact `"1"^^xsd:nonNegativeInteger`
  literal (same convention as cls-maxc2), fires only on data-side
  restrictions carrying `onClass`. The known-narrow anchor rewrite in
  `OWL.QueryRewrite.fst` (#236) matches on maxQualifiedCardinality
  restrictions too — confirm the new closure triples don't change the
  entailment-regime parent7 answer (they add a bnode-typed membership
  for the *filler*, not the parent, so they should not).

### 2.5 WebOnt-I5.8-008 / WebOnt-I5.8-009 — missing XSD range-intersection rule

- **Missing conclusion triples:**
  `<premises008#p> rdfs:range xsd:unsignedShort` and
  `<premises009#p> rdfs:range xsd:short` (exact IRI triples — no bnodes,
  no matcher involvement).
- **Premises:** 008: `p rdfs:range xsd:short` + `p rdfs:range
  xsd:unsignedInt`. 009: `p rdfs:range xsd:nonNegativeInteger` +
  `p rdfs:range xsd:nonPositiveInteger`.
- **Root cause: missing rule.** The XSD tower
  (`xsd_hierarchy_edges`, 3539) plus `scm-rng2` (3623) only propagate
  ranges **upward**. Both conclusions sit **below** each premise
  datatype: they are the *intersection* of the two ranges
  (short ∩ unsignedInt = [0, 32767] ⊆ unsignedShort;
  nonNegativeInteger ∩ nonPositiveInteger = {0} ⊆ byte, and byte ⊑
  short lifts it). Two `rdfs:range` axioms on one property constrain
  values to the intersection of the value spaces, so asserting any
  datatype whose value space contains that intersection is sound.
  Needs a finite table rule; the existing tower then finishes 009 via
  scm-rng2.

**Fix sketch** (slot after `owl_rule_xsd_datatype_axioms` (g25); the
fixpoint's next iteration gives scm-rng2 the byte → short lift for 009):

```fstar
// Sound intersection entries: value-space(d1) intersected with
// value-space(d2) is contained in value-space of every listed output.
let xsd_range_intersections : list (wf_iri & wf_iri & list wf_iri) =
  [ (xsd_short, xsd_unsignedInt,  [xsd_unsignedShort]);   // [0,32767]
    (xsd_short, xsd_unsignedLong, [xsd_unsignedShort]);
    (xsd_byte,  xsd_unsignedInt,  [xsd_unsignedByte]);
    (xsd_nonNegativeInteger, xsd_nonPositiveInteger, [xsd_byte; xsd_unsignedByte]) ] // value space is exactly zero

// dt-rng-intersect (sound extension): if P carries rdfs:range on both
// datatypes of a table entry (either order), emit the entry's outputs
// as additional ranges. scm-rng2 + the tower close upward from there.
let owl_rule_dt_range_intersect (g : rdf_graph) (ig : indexed_graph) : rdf_graph =
  List.Tot.fold_left
    (fun (acc : rdf_graph) (t : triple) ->
      if t.p = rdfs_range then
        match t.o with
        | T_IRI d1 ->
          List.Tot.fold_left
            (fun (acc1 : rdf_graph) (d2_term : rdf_term) ->
              match d2_term with
              | T_IRI d2 ->
                List.Tot.fold_left
                  (fun (acc2 : rdf_graph) (entry : (wf_iri & wf_iri & list wf_iri)) ->
                    let (e1, e2, outs) = entry in
                    if (e1 = d1 && e2 = d2) || (e1 = d2 && e2 = d1) then
                      List.Tot.fold_left
                        (fun (acc3 : rdf_graph) (d3 : wf_iri) ->
                          add_triple_unchecked acc3 ({ s = t.s; p = rdfs_range; o = T_IRI d3 }))
                        acc2 outs
                    else acc2)
                  acc1 xsd_range_intersections
              | _ -> acc1)
            acc (find_objects_indexed ig t.s rdfs_range)
        | _ -> acc
      else acc)
    g g
```

- **Risk: low.** Fires only on *pairs* of ranges present in the table.
  Checked against the passing NE test WebOnt-I5.8-007
  (`range xsd:short` must NOT entail `range xsd:unsignedByte`): a
  single range never matches a pair entry, and no entry output is
  below the true intersection, so 007 stays a pass. The table is
  deliberately test-backed, not the full 12-type product; extending it
  later is mechanical.

### 2.6 WebOnt-I5.5-005 / WebOnt-I5.26-010 — OWL 1 Full comprehension; recommend accepting as fails

- **Missing conclusion triples:**
  `_:rdfxml_b0 <owl:unionOf> _:rdfxml_b1` (I5.5-005: from the single
  premise `Class(a)`, conclude a class equal to `unionOf (a)` exists)
  and `_:n <rdf:type> <owl:Restriction>` (I5.26-010: from
  `ObjectProperty(p)` alone, conclude the restriction `p min 1`
  exists).
- **Root cause: neither a missing RL rule nor a matcher bug — these
  are comprehension-principle entailments.** The premises assert
  nothing about any individual; the conclusions assert the *existence
  of a class expression*. That holds under OWL 1 Full's comprehension
  conditions (which guaranteed every describable class expression a
  denotation), and these WebOnt tests were approved in that era. The
  OWL 2 RDF-Based Semantics dropped the comprehension conditions
  (they survive only as an informative appendix), and OWL 2 RL's PR1
  theorem never covered bnode conclusions in the first place. No rule
  in the RL table — and no sound Horn rule over the premise vocabulary
  — produces these triples from these premises; a "fix" would be a
  generator that emits, for every named class, a singleton-unionOf
  scaffold (4 triples), and for every named object property, a min-1
  restriction scaffold (3 triples), purely to feed the matcher.
- **Assessment: not worth fixing, say so on the dashboard instead.**
  The generator route is cheap (deterministic `__rl_` bnodes, bounded
  by the count of named classes/properties) but it is junk-triple
  manufacturing in service of two legacy tests whose entailments the
  OWL 2 semantics no longer supports; it also grows every closure on
  every graph (the exact opposite of the #262 direction). Recommended
  disposition: leave failing, and annotate the dashboard's OWL section
  with "2 of the 10 PE failures are OWL 1 Full comprehension tests
  (I5.5-005, I5.26-010), intentionally not implemented". If a later
  session wants the score anyway, the generator shape is the
  `owl_rule_minc1_bridge` pattern (3397) gated on named entities, and
  it must be documented in CLAUDE.md's "Known sound-but-narrow
  rewrites" section — comprehension is only sound relative to the
  OWL 1 Full reading.

### 2.7 New-Feature-ObjectPropertyChain-BJP-002 — FAIL/no-premise is a manifest-syntax gap, not a bug

- **Runner outcome:** `FAIL/no-premise` — `run_positive_entailment`
  (owl_runner.ml:505) returns this when `info.premise = None`.
- **Root cause: the catalog entry has no RDF/XML premise at all.** The
  TestCase block carries only `test:fsPremiseOntology` /
  `test:fsConclusionOntology` (OWL 2 *functional syntax*:
  `TransitiveObjectProperty(:p)` entails
  `SubObjectPropertyOf(ObjectPropertyChain(:p :p) :p)`), with
  `test:normativeSyntax test:FUNCTIONAL` and **no**
  `test:rdfXmlPremiseOntology` triple. The runner only harvests the
  `rdfXml*` predicates (build_index, owl_runner.ml:239–260), so
  "no-premise" is the accurate description of what the harness can
  see. The other 29 PE entries all carry rdfXml literals; this is the
  only FUNCTIONAL-only one.
- **Fix shape (two honest options, neither is a closure rule):**
  1. **F\* functional-syntax parser** (iron rule #4: parsers belong in
     F\*): a `Parser.OWLFunctional.fst` handling the declaration/axiom
     subset these catalogs use, extracted and called from the runner
     when `rdfXml*` is absent. Entailment then also needs the converse
     of `owl_rule_chain_to_transitive` (3195) — transitive P entails
     chain (P P) ⊑ P — which is a 10-line rule emitting the
     propertyChainAxiom list scaffold with `__rl_` list bnodes. Real
     but non-trivial work; file as its own issue.
  2. **Score-hygiene stopgap:** a distinct outcome
     `SKIP/functional-syntax-only` counted outside pass/fail, with the
     denominator reported as "29 RDF/XML + 1 functional-syntax-only".
     Per anti-pattern #3 the label must be explicit — silently dropping
     the test to 29 is banned.
  Recommended: option 2 now (one enum + one printf in the runner's
  I/O-glue layer, no semantics), option 1 as the tracked issue.

## 3. Suggested commit sequence

Each commit is one subagent-sized deliverable (anti-pattern #23) and is
gated on, in labelled full-sentence form: the profile-RL catalog all
four sections (PE currently 20 pass, 10 fail of 30; NE 3 pass, 3 fail
of 6; Cons 75 pass, 1 fail of 76; Inc 4 pass, 10 fail of 14), the
SPARQL 1.1 entailment-regime suite (70 pass of 70 must hold), and the
full W3C SPARQL (631 of 631) and RDF (1031 of 1031) suites. All F\*
verification under the fstar opam switch, no `--lax`.

1. **Commit 1 — class-disjointness cluster** (§2.2 expansion +
   §2.1 complement scaffold, plus the `owl_AllDisjointClasses_iri` /
   `owl_members_iri` constants). Expected: PE 22 pass, 8 fail (out of
   30). Watch Cons/Inc for newly honest inconsistency detections from
   the pairwise disjointWith facts.
2. **Commit 2 — property-disjointness cluster** (§2.3: AllDisjointProperties
   expansion, shared-value contrapositive, differentFrom→AllDifferent
   materialisation + `owl_AllDifferent_iri`). Expected: PE 24 pass, 6
   fail (out of 30). Re-measure the ConsistencyTest section wall time —
   this commit is the #262-sensitive one; if the two existing 30 s cap
   trips multiply, hold it until the sameAs snapshot-cluster fix lands.
3. **Commit 3 — max-qualified contrapositive** (§2.4). Expected: PE 25
   pass, 5 fail (out of 30). Re-run the entailment-regime parent7
   family explicitly (interaction with the #236 anchor rewrite).
4. **Commit 4 — XSD range intersection** (§2.5). Expected: PE 27 pass,
   3 fail (out of 30) with WebOnt-I5.8-007 still passing in the NE
   section.
5. **Commit 5 — runner outcome hygiene** (§2.7 option 2, owl_runner.ml
   only): `SKIP/functional-syntax-only` for BJP-002, reported as
   "27 pass, 2 fail (out of 29 RDF/XML tests), 1 skipped
   (functional-syntax-only)". File the F\* functional-syntax parser
   (§2.7 option 1) and the comprehension-tests disposition (§2.6) as
   issues in the same PR; update the dashboard annotation per §2.6.

End state: 27 pass, 2 fail, 1 skip — with both residual fails
(I5.5-005, I5.26-010) documented as OWL 1 Full comprehension
entailments deliberately outside our OWL 2 RL closure, and the skip
tracked by a parser issue rather than hidden in the denominator.

## 4. Summary table

| Test | Root cause | Fix | Difficulty |
|---|---|---|---|
| DisjointClasses-001 | no complementOf-scaffold rule | new rule cax-dw-comp (§2.1) | low |
| DisjointClasses-003 | + no AllDisjointClasses expansion | new rule cax-adc-expand (§2.2) + §2.1 | low |
| New-Feature-DisjointDataProperties-002 | no ADP expansion, no shared-value pdw contrapositive, no AllDifferent surface form | three new rules (§2.3) | medium |
| New-Feature-DisjointObjectProperties-002 | no ADP expansion, no AllDifferent surface form | §2.3 rules 1 + 3 (rule 2 not needed) | medium |
| New-Feature-ObjectQCR-002 | no max-1-qualified contrapositive | new rule cls-maxqc-comp (§2.4) | medium |
| WebOnt-I5.8-008 | ranges only propagate up the XSD tower | dt-rng-intersect table rule (§2.5) | low |
| WebOnt-I5.8-009 | same, intersection is the zero singleton | §2.5 entry + existing scm-rng2 lift | low |
| WebOnt-I5.5-005 | OWL 1 Full comprehension (unionOf) | accept as fail, annotate (§2.6) | n/a |
| WebOnt-I5.26-010 | OWL 1 Full comprehension (min-1 restriction) | accept as fail, annotate (§2.6) | n/a |
| New-Feature-ObjectPropertyChain-BJP-002 | catalog entry is functional-syntax-only; runner reads only rdfXml literals | SKIP outcome now; F\* functional-syntax parser issue (§2.7) | low now / high later |
