/-
L4Factoidal.ShEx.Satisfies — `satisfies(n, se, G)` with the schema in
scope, so shape REFERENCES resolve.

`Shapes.lean` decides a shape against a neighbourhood and stops at a
reference: `arcSatisfiesValueExpr` returns `false` for `.ref` and
`.shape`, and `matchTripleExpr` returns `none` for a `TripleExpr.ref`.
Its module header says so. That is the right boundary for a module
that does not have the schema — but the ShEx test suite is largely
made of references, so nothing above it can be scored without this
layer.

The generalisation is two parameters: the value check, and the lookup
that resolves a triple-expression inclusion (`&<label>`). Everything
else is the same algorithm — `Shapes.satisfiesShapeGen` is called with
both supplied, so the partition search and the EXTRA/CLOSED
distinction its header exists to keep straight are reused, not
re-derived.

## Recursion terminates on the (label, node) pair, not on fuel

A ShEx schema may be recursive (`<S> { <p> @<S> }`), and a recursive
schema against a cyclic graph can walk forever.

This module used to bound the walk with a fuel counter, `refDepth = 6`,
and answer `false` when it ran out. Its header called that a REFUSAL
and said "the runner counts it separately". **The runner did no such
thing**: `validateNode` returned a `Bool`, `Harness/ShExRun.lean`
compared it against the expected verdict, and there was no declined
column anywhere. Sixteen entries of the validation suite were scored
as validation failures for running out of fuel — including
`<S1> { <p1> BNODE @<S1> OR MINLENGTH 20 @<S1> }` against a reflexive
triple, the three-cycle `S1 → S2 → S3 → S1`, and `1list0PlusDot`
walking a three-element RDF list, which needs depth 8. A cap that
answers a question it did not decide is a wrong answer, and a comment
claiming someone else counts it is worse than no comment.

The bound is now the (shape label, focus node) pair. `satisfiesIn`
carries the pairs already being decided further up the stack; entering
`@<S>` for a node already on the stack ASSUMES the shape holds of it
and returns `true`. Every `.ref` step either returns at once or adds a
new pair, and the pairs come from the schema's labels crossed with the
graph's terms, so the walk terminates with no cap to exhaust. Nothing
is refused, and no declined column is needed.

**The assumption is the GREATEST fixpoint reading**, and it is sound
only for a schema whose recursion does not pass through `ShapeNot`
(negation stratification, ShEx 2.1 §5.9). This module does not check
that condition. A schema that violates it gets the greatest-fixpoint
answer, which may differ from the least-fixpoint one; the corpus
contains no such schema.
-/
import L4Factoidal.ShEx.Shapes

namespace L4Factoidal.ShEx

open L4Factoidal.RDF

/-! ## Resolving a triple-expression INCLUSION

`&<label>` names a triple expression declared elsewhere in the schema,
by an `id` on a `TripleConstraint`, an `EachOf` or a `OneOf`.
`Shapes.matchStates` takes the lookup as a parameter because the
schema is not in scope there; here it is, so the search below walks
every shape declaration for the label. `TripleExpr.ref` used to answer
`none` from the matcher, which reads as UNSATISFIED — an inclusion was
scored as a failed shape.
-/

mutual

/-- The triple expression with this `id` inside a shape expression. -/
partial def findTeInShapeExpr (id : String) : ShapeExpr → Option TripleExpr
  | .shape sh    => sh.expression.bind (findTeInTripleExpr id)
  | .shapeAnd es => es.findSome? (findTeInShapeExpr id)
  | .shapeOr es  => es.findSome? (findTeInShapeExpr id)
  | .shapeNot e  => findTeInShapeExpr id e
  | _            => none

/-- The triple expression with this `id` inside a triple expression. -/
partial def findTeInTripleExpr (id : String) : TripleExpr → Option TripleExpr
  | te@(.tripleConstraint tc) =>
      if tc.id == some id then some te
      else tc.valueExpr.bind (findTeInShapeExpr id)
  | te@(.eachOf g) =>
      if g.id == some id then some te
      else g.expressions.findSome? (findTeInTripleExpr id)
  | te@(.oneOf g) =>
      if g.id == some id then some te
      else g.expressions.findSome? (findTeInTripleExpr id)
  | .ref _ => none

end

/-- Resolve a triple-expression label declared anywhere in the schema. -/
def Schema.tripleExpr (sch : Schema) (id : String) : Option TripleExpr :=
  sch.shapes.findSome? (fun d => findTeInShapeExpr id d.expr)

/-! ## EXTENDS

ShEx 2.1's `EXTENDS` is not conjunction. `<C> EXTENDS @<B> { <p> . }`
does not ask the node to satisfy `<B>` and `<C>` separately over the
same neighbourhood; it asks for ONE partition of the neighbourhood
shared out across the whole ancestor chain — the `M = M' ⊎ ⊎_{x∈anc(X)} M_x`
rule of the inheritance formalisation (arXiv 2503.24299, Table 3
line 18), which `formal/fstar/ShEx.Validation.fst:1190` implements and
this follows.

`ExtendsFlat` collects, from a shape and everything it extends: the
triple expressions each contributes, the union of the `extra`
predicates, whether ANY of them is `closed`, and the node-level checks
(a node constraint, a `ShapeOr`, a `ShapeNot`, an `EXTERNAL`) that are
decided against the node rather than against the neighbourhood.

DIAMOND DEDUP: a label already on the flattening path contributes
nothing the second time. `extends-closed-diamond.shex` has
`<BOTTOM> EXTENDS @<G0-0> EXTENDS @<G0-1>` where both extend `<G0>`;
without the dedup `<G0>`'s own constraint would be folded in twice and
would silently require two matching triples where the schema asks for
one.

INTERPRETATION RECORDED (2026-08-26): the split is TWO-TIER, not a
flat N-way partition, following the F* module.

* The derived shape's OWN expression claims its arcs first and
  exclusively.
* Every ancestor in the flattened chain then sees the SAME leftover
  pool, independently of the other ancestors. An arc is explained when
  SOME chain member's chosen match claims it, not when every member
  does — so `<B> @<A> AND { ... }` lets one triple satisfy an
  ancestor's bound and a sibling restriction at once, while
  `EXTENDS @<E> EXTENDS @<F>` still partitions by value-disjointness,
  because a member only ever claims candidates its own value
  expression accepts.

`ABSTRACT` (Definition 4 of the same formalisation) is applied where a
shape is reached by REFERENCE: a node satisfies an abstract shape only
by satisfying some non-abstract shape that extends it. It is NOT
applied to a validation request that names the abstract shape
directly, because the corpus asks for exactly that and expects an
answer (`vitals-RESTRICTS-pass_lie-Vital` names `ABSTRACT <#Vital>`).

## Known gap: one over-permissive chain residue

`ExtendAND3G-fail_ExtraP` still answers `true` where the corpus says
`false`. `<E> EXTENDS @<D> { <p> [2] }` against `<p> 0, 2, 3`: the own
tier claims the `2`, and in the residue `{0, 3}` the ancestor `<C>`
cannot take the `3` — but `<A>`, whose value set does take it, is
allowed to explain it under the "SOME member claims it" rule above.
Requiring EVERY member's own residue to be acceptable instead fixes
this one entry and costs thirteen others (measured 2026-08-26: 1153
pass, 26 fail against 1165 pass, 14 fail), so it is the wrong repair.
The F* module carries an extra `unbounded_tes` argument through
`matches_chain_shared` that this port does not have, and that is the
first place to look.
-/

/-- What a shape and its ancestors jointly contribute. -/
structure ExtendsFlat where
  tes    : List TripleExpr := []
  extra  : List String := []
  closed : Bool := false
  checks : List ShapeExpr := []

def ExtendsFlat.combine (a b : ExtendsFlat) : ExtendsFlat :=
  { tes := a.tes ++ b.tes, extra := a.extra ++ b.extra,
    closed := a.closed || b.closed, checks := a.checks ++ b.checks }

mutual

/-- Flatten one shape expression into what it contributes. `visited`
    carries the labels already folded in, so a diamond counts each
    ancestor once. -/
partial def flattenSE (sch : Schema) (se : ShapeExpr) (visited : List String)
    : Option (ExtendsFlat × List String) :=
  match se with
  | .shape sh =>
      let own : ExtendsFlat :=
        { tes := (match sh.expression with | some te => [te] | none => [])
          extra := sh.extra, closed := sh.closed, checks := [] }
      if sh.extendsRefs.isEmpty then some (own, visited)
      else
        (match resolveExtends sch sh.extendsRefs visited with
         | some (parent, v1) => some (own.combine parent, v1)
         | none              => none)
  | .shapeAnd es => flattenSEList sch es visited
  | .ref label =>
      if visited.contains label then some ({}, visited)
      else
        (match sch.lookup label with
         | some d => flattenSE sch d.expr (label :: visited)
         | none   => none)
  | _ => some ({ checks := [se] }, visited)

partial def flattenSEList (sch : Schema) (ses : List ShapeExpr) (visited : List String)
    : Option (ExtendsFlat × List String) :=
  match ses with
  | []      => some ({}, visited)
  | hd :: tl =>
      match flattenSE sch hd visited with
      | none          => none
      | some (a, v1)  =>
          match flattenSEList sch tl v1 with
          | none         => none
          | some (b, v2) => some (a.combine b, v2)

/-- Flatten a list of `extends` labels. -/
partial def resolveExtends (sch : Schema) (labels : List String) (visited : List String)
    : Option (ExtendsFlat × List String) :=
  match labels with
  | []      => some ({}, visited)
  | hd :: tl =>
      if visited.contains hd then resolveExtends sch tl visited
      else
        match sch.lookup hd with
        | none   => none
        | some d =>
            match flattenSE sch d.expr (hd :: visited) with
            | none         => none
            | some (a, v1) =>
                match resolveExtends sch tl v1 with
                | none         => none
                | some (b, v2) => some (a.combine b, v2)

end

/-- The labels a shape expression EXTENDS directly. -/
partial def directExtends : ShapeExpr → List String
  | .shape sh    => sh.extendsRefs
  | .shapeAnd es => es.flatMap directExtends
  | _            => []

/-- Does an extends chain starting at `labels` reach `target`? -/
partial def reachesLabel (sch : Schema) (target : String) (labels : List String)
    (seen : List String) : Bool :=
  labels.any (fun l =>
    l == target ||
    (!(seen.contains l) &&
      (match sch.lookup l with
       | some d => reachesLabel sch target (directExtends d.expr) (l :: seen)
       | none   => false)))

/-- Every chain member sees the same `pool`; `running` is the set of
    arcs NO member has claimed yet, and the residue that survives all
    of them must pass `acceptable`. -/
partial def chainResidueOk (valueOk : Option ShapeExpr → Term → Bool)
    (lookupTe : String → Option TripleExpr) (arr : Array Arc)
    (members : List TripleExpr) (pool running : List Nat)
    (acceptable : List Nat → Bool) : Bool :=
  match members with
  | []      => acceptable running
  | m :: ms =>
      (matchStates valueOk lookupTe arr m pool).any (fun leftM =>
        chainResidueOk valueOk lookupTe arr ms pool
          (running.filter (fun i => leftM.contains i)) acceptable)

mutual

/-- `satisfies(n, se, G)`.

    `visited` carries the (shape label, node) pairs already being
    decided further up the stack. Re-entering one ASSUMES it holds —
    see the module header for why, and for the stratification
    condition that makes the assumption sound. -/
partial def satisfiesIn (sch : Schema) (g : List Triple)
    (visited : List (String × Term)) (se : ShapeExpr) (n : Term) : Bool :=
  let valueOk : Option ShapeExpr → Term → Bool := fun ve t =>
    match ve with
    | none    => true
    | some e' => satisfiesIn sch g visited e' t
  match se with
  | .ref id =>
      if visited.contains (id, n) then true
      else
        (match sch.lookup id with
         | none   => false
         | some d =>
             let v := (id, n) :: visited
             satisfiesIn sch g v d.expr n
             -- ABSTRACT (arXiv 2503.24299, Definition 4): a node
             -- satisfies an abstract shape only by satisfying some
             -- NON-abstract shape that extends it. Without this,
             -- `ABSTRACT <PersonShape> { ... }` — which is not closed —
             -- admitted a node carrying an extra predicate that its
             -- only concrete extension, a CLOSED `<UserShape>`, rejects.
             && (!d.isAbstract
                 || sch.shapes.any (fun d2 =>
                      !d2.isAbstract
                      && reachesLabel sch id (directExtends d2.expr) []
                      && satisfiesIn sch g v d2.expr n)))
  | .shapeAnd es       => es.all (fun e => satisfiesIn sch g visited e n)
  | .shapeOr es        => es.any (fun e => satisfiesIn sch g visited e n)
  | .shapeNot e        => !(satisfiesIn sch g visited e n)
  | .nodeConstraint nc => satisfiesNodeConstraint nc n
  | .shape sh          =>
      if sh.extendsRefs.isEmpty then
        satisfiesShapeGen valueOk sch.tripleExpr sh (neighbourhood g n)
      else satisfiesExtends sch g visited sh n
  | .external          => false

/-- §satisfies for a shape that EXTENDS others — see the EXTENDS
    section above for the partition rule and the two-tier split. -/
partial def satisfiesExtends (sch : Schema) (g : List Triple)
    (visited : List (String × Term)) (sh : Shape) (n : Term) : Bool :=
  match resolveExtends sch sh.extendsRefs [] with
  | none => false
  | some (chain, _) =>
      let valueOk : Option ShapeExpr → Term → Bool := fun ve t =>
        match ve with
        | none    => true
        | some e' => satisfiesIn sch g visited e' t
      let allExtra := sh.extra ++ chain.extra
      let allClosed := sh.closed || chain.closed
      let allTes := (match sh.expression with | some te => [te] | none => []) ++ chain.tes
      let pairs := allTes.flatMap (mentionedPairsWith sch.tripleExpr)
      let arcs := neighbourhood g n
      let unmentioned := arcs.filter (fun a =>
        !a.inverse && !(pairs.contains (false, a.predicate))
          && !(allExtra.contains a.predicate))
      if anySemActFails sh.semActs then false
      else if allClosed && !unmentioned.isEmpty then false
      else if !(chain.checks.all (fun c => satisfiesIn sch g visited c n)) then false
      else
        let arr := arcs.toArray
        let all := List.range arcs.length
        let acceptable : List Nat → Bool := fun rest =>
          (rest.filterMap (fun i => arr[i]?)).all (fun a =>
            a.inverse || !(pairs.contains (false, a.predicate))
            || allExtra.contains a.predicate)
        let ownStates := match sh.expression with
          | some te => matchStates valueOk sch.tripleExpr arr te all
          | none    => [all]
        ownStates.any (fun rest =>
          chainResidueOk valueOk sch.tripleExpr arr chain.tes rest rest acceptable)

end

/-- Validate a focus node against a labelled shape of a schema. -/
def validateNode (sch : Schema) (g : List Triple) (label : String) (n : Term) : Bool :=
  if anySemActFails sch.startActs then false else
  match sch.lookup label with
  | some d => satisfiesIn sch g [(label, n)] d.expr n
  | none   => false

/-- Validate a focus node against the schema's START shape.

    A manifest entry with no `shape` names the start shape, which is a
    shape EXPRESSION and not a label: `Schema.lookup ""` cannot find
    it and answered `false` for every such entry. -/
def validateStart (sch : Schema) (g : List Triple) (n : Term) : Bool :=
  if anySemActFails sch.startActs then false else
  match sch.start with
  | some se => satisfiesIn sch g [] se n
  | none    => false

end L4Factoidal.ShEx
