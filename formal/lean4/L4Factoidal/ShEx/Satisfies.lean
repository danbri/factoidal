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

/-- The triple expression with this `id` inside a shape expression.

    The `Shape`/`Group`/`TripleConstraint` records are single-constructor
    INDUCTIVES, not structures, so a field accessor (`sh.expression`) is
    a match the equation compiler cannot see through. Matching the
    constructor is what makes the recursion structural. -/
def findTeInShapeExpr (id : String) : ShapeExpr → Option TripleExpr
  | .shape (.mk _ _ expr _ _ _) =>
      (match expr with
       | some te => findTeInTripleExpr id te
       | none    => none)
  | .shapeAnd es => findTeInShapeExprList id es
  | .shapeOr es  => findTeInShapeExprList id es
  | .shapeNot e  => findTeInShapeExpr id e
  | _            => none

/-- `findSome?` over a list of shape expressions, written out so the
    recursion is structural (rule: a higher-order `findSome?` hides
    the decrease from the equation compiler). -/
def findTeInShapeExprList (id : String) : List ShapeExpr → Option TripleExpr
  | []      => none
  | e :: r  =>
      (match findTeInShapeExpr id e with
       | some te => some te
       | none    => findTeInShapeExprList id r)

/-- The triple expression with this `id` inside a triple expression. -/
def findTeInTripleExpr (id : String) : TripleExpr → Option TripleExpr
  | te@(.tripleConstraint (.mk tcId _ _ ve _ _ _ _)) =>
      if tcId == some id then some te
      else
        (match ve with
         | some se => findTeInShapeExpr id se
         | none    => none)
  | te@(.eachOf (.mk gId ges _ _ _ _)) =>
      if gId == some id then some te
      else findTeInTripleExprList id ges
  | te@(.oneOf (.mk gId ges _ _ _ _)) =>
      if gId == some id then some te
      else findTeInTripleExprList id ges
  | .ref _ => none

/-- `findSome?` over a list of triple expressions, written out. -/
def findTeInTripleExprList (id : String) : List TripleExpr → Option TripleExpr
  | []     => none
  | e :: r =>
      (match findTeInTripleExpr id e with
       | some te => some te
       | none    => findTeInTripleExprList id r)

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

An unbounded chain member may CLAIM an arc that no other unbounded
member would accept, but that claim does not COUNT as explaining it —
see `backgroundSafe` for the rule and for the pair of fixtures that
turn on it alone.
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
def directExtends : ShapeExpr → List String
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

/-- Is this chain member an UNBOUNDED triple constraint? -/
def teIsUnboundedTc : TripleExpr → Bool
  | .tripleConstraint tc => tc.unbounded
  | _                    => false

/-- Would this member accept the arc — or does it not claim that
    (inverse, predicate) pair at all? -/
def itemGoodFor (valueOk : Option ShapeExpr → Term → Bool)
    (te : TripleExpr) (a : Arc) : Bool :=
  match te with
  | .tripleConstraint tc =>
      !(arcMatchesPredicate tc a) || valueOk tc.valueExpr a.value
  | _ => true

/-- An arc is BACKGROUND SAFE when every unbounded chain member would
    accept it — the intersection of the broad ancestors' value sets.

    An unbounded member may claim an arc no other unbounded member
    accepts, but that claim must not COUNT as explaining the arc:
    only a genuinely bounded sibling's exact claim can. `ExtendAND3G`
    and `Extend3G` differ in exactly this and in nothing else. `<D>`,
    with `<p> [0 1 2 3 5 6 7 8 9]+`, structurally tolerates the value
    `3` in both; in `Extend3G` the bounded `<F>` pins `3` with its own
    `<p> [3]`, and in `ExtendAND3G` nothing does, so `<D>` absorbing
    `3` gratuitously must not excuse it.

    Empty list means there are no unbounded members at all, so nothing
    is unconditionally excused — a different case from every member of
    a non-empty list accepting the arc. -/
def backgroundSafe (valueOk : Option ShapeExpr → Term → Bool)
    (unbounded : List TripleExpr) (a : Arc) : Bool :=
  !unbounded.isEmpty && unbounded.all (fun te => itemGoodFor valueOk te a)

/-- Every chain member sees the same `pool`; `running` is the set of
    arcs NO member has claimed yet, and the residue that survives all
    of them must pass `acceptable`. An unbounded member's claim on an
    arc that is not background safe is handed BACK into its own
    leftover, so it does not shrink `running`. -/
def chainResidueOk (valueOk : Option ShapeExpr → Term → Bool)
    (lookupTe : String → Option TripleExpr) (arr : Array Arc)
    (unbounded : List TripleExpr)
    (members : List TripleExpr) (pool running : List Nat)
    (acceptable : List Nat → Bool) : Bool :=
  match members with
  | []      => acceptable running
  | m :: ms =>
      (matchStates valueOk lookupTe arr m pool).any (fun leftM =>
        let effective :=
          if teIsUnboundedTc m then
            pool.filter (fun i =>
              leftM.contains i ||
              (match arr[i]? with
               | some a => !(backgroundSafe valueOk unbounded a)
               | none   => false))
          else leftM
        chainResidueOk valueOk lookupTe arr unbounded ms pool
          (running.filter (fun i => effective.contains i)) acceptable)

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
  | .ref id => satisfiesLabel sch g visited id n
  | .shapeAnd es       => es.all (fun e => satisfiesIn sch g visited e n)
  | .shapeOr es        => es.any (fun e => satisfiesIn sch g visited e n)
  | .shapeNot e        => !(satisfiesIn sch g visited e n)
  | .nodeConstraint nc => satisfiesNodeConstraint nc n
  | .shape sh          =>
      if sh.extendsRefs.isEmpty then
        satisfiesShapeGen valueOk sch.tripleExpr sh (neighbourhood g n)
      else satisfiesExtends sch g visited sh n
  | .external          => false

/-- Does the node validate against a shape LABEL?

    DESCENDANT-WITNESS SEMANTICS (arXiv 2503.24299, Definition 4; the
    same rule `formal/fstar/ShEx.Validation.fst:1035` records as
    verified against @shexjs/validator 1.0.0-alpha.29). A node
    validates against a label when

    * the label is NON-abstract and the node satisfies the label's own
      declared shape expression, OR
    * SOME non-abstract declaration that extends the label, directly or
      transitively, validates the node.

    A correct typing is closed under ancestors, so witnessing
    `(t, ReclinedBP)` also witnesses `(t, BP)`, `(t, Posture)`,
    `(t, Vital)` up the whole chain. An ABSTRACT label offers ONLY the
    second route — its own-content check is skipped outright, which is
    what makes `ABSTRACT <PersonShape>` reject a node that satisfies
    its own content while neither concrete descendant accepts it.

    The witness route for a NON-abstract label is what makes
    `vitals-RESTRICTS-pass_lie-Posture` pass: `:lie` fails
    `<#Posture>`'s own expression outright — the systolic and diastolic
    components are mentioned-predicate leftovers with no `extra` to
    excuse them, which is the strict rule `1val1IRIREF_v1v2` and
    `1dotInline1_overReferrer` require — but non-abstract
    `<#ReclinedBP>` extends-reaches `<#Posture>` and validates `:lie`,
    so `(lie, Posture)` is witnessed. -/
partial def satisfiesLabel (sch : Schema) (g : List Triple)
    (visited : List (String × Term)) (label : String) (n : Term) : Bool :=
  if visited.contains (label, n) then true
  else
    match sch.lookup label with
    | none   => false
    | some d =>
        let v := (label, n) :: visited
        (!d.isAbstract && satisfiesIn sch g v d.expr n)
        || sch.shapes.any (fun d2 =>
             !d2.isAbstract
             && reachesLabel sch label (directExtends d2.expr) []
             && satisfiesIn sch g v d2.expr n)

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
        let unbounded := chain.tes.filter teIsUnboundedTc
        ownStates.any (fun rest =>
          chainResidueOk valueOk sch.tripleExpr arr unbounded chain.tes rest rest acceptable)

end

/-- Validate a focus node against a labelled shape of a schema. -/
def validateNode (sch : Schema) (g : List Triple) (label : String) (n : Term) : Bool :=
  if anySemActFails sch.startActs then false else
  satisfiesLabel sch g [] label n

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
