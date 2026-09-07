/-
L4Factoidal.RDF.GraphPatterns — configurable named-graph IRI patterns.

A design sketch for
`docs/designissues/2026-09-07-hierarchical-named-graphs.md`.

RDF 1.1 Concepts section 4 says a graph name is an IRI or a blank node and
assigns NO relation between the graphs of a dataset: "the RDF Dataset does
not itself imply any relationship between the graphs". Anything a store
wants to read off graph names is therefore a LOCAL declaration, not RDF, and
this module is that declaration made explicit: a small subset of RFC 6570
level-1 URI templates, a matcher, a composition order over the matched IRI
STRINGS, and the view of a dataset the order induces.

Nothing here is imported by another module yet. It carries types, total
definitions and theorem STATEMENTS; the statements that are not definitional
are `Prop`-valued `def`s so that no `sorry` enters the tree (project rule:
nothing with `sorry` is committed).

No `partial`, no `unsafe`, no `sorry`, no `native_decide`.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RDF.GraphPatterns

open L4Factoidal.RDF

/-! ## 1. The pattern language

RFC 6570 section 1.2 level 1, restricted further:

* an expression is `{name}` and nothing else — no operator, no modifier, no
  explode, no list value;
* an expansion never contains `/`, so the segment structure of the IRI is
  fixed by the template and not by the values (RFC 3986 section 3.3 makes
  `/` the path segment delimiter, and RFC 6570 level-1 expansion percent-
  encodes it, so this restriction is a check rather than a new rule);
* a template is a literal, then an alternation of variables and literals;
* two variables are never adjacent (otherwise matching is ambiguous).
-/

/-- One piece of a template. -/
inductive Seg where
  | lit (text : String)
  | var (name : String)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A template: `https://s.example/g/{scheme}/c/{concept}` is
`[lit "https://s.example/g/", var "scheme", lit "/c/", var "concept"]`. -/
structure Template where
  segs : List Seg
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The syntactic restriction above, decided. A template is well formed when
it starts with a non-empty literal, has no empty literal, has no two adjacent
variables, and repeats no variable name. -/
def Template.wf (t : Template) : Bool :=
  let rec noAdjacent : List Seg → Bool
    | [] => true
    | .var _ :: .var _ :: _ => false
    | .lit "" :: _ => false
    | _ :: rest => noAdjacent rest
  let names := t.segs.filterMap (fun s => match s with | .var n => some n | _ => none)
  (match t.segs with | .lit l :: _ => l != "" | _ => false)
    && noAdjacent t.segs
    && names.length == names.eraseDups.length

/-- Variable bindings produced by a match, in template order. -/
abbrev Bindings := List (String × String)

/-- Match a template's segments against the characters of an IRI. A variable
consumes the longest run of characters that is not `/` and is not empty; a
literal must match exactly. Structural recursion on the segment list, so the
function is total. -/
def matchSegs : List Seg → List Char → Option Bindings
  | [], [] => some []
  | [], _ :: _ => none
  | .lit l :: rest, cs =>
      let lc := l.toList
      if lc.isPrefixOf cs then matchSegs rest (cs.drop lc.length) else none
  | .var v :: rest, cs =>
      let value := cs.takeWhile (fun c => c != '/')
      let tail := cs.dropWhile (fun c => c != '/')
      if value.isEmpty then none
      else (matchSegs rest tail).map (fun bs => (v, String.mk value) :: bs)

/-- Match one template against an IRI string. -/
def Template.match? (t : Template) (iri : String) : Option Bindings :=
  matchSegs t.segs iri.toList

/-- RFC 6570 expansion, level 1, for the values a match produced. `none` when
a variable of the template has no binding. -/
def Template.expand? (t : Template) (b : Bindings) : Option String :=
  t.segs.foldl (fun acc s =>
    match acc, s with
    | none, _ => none
    | some out, .lit l => some (out ++ l)
    | some out, .var v =>
        match b.lookup v with
        | some value => some (out ++ value)
        | none => none) (some "")

/-- `parent` is a structural prefix of `child`: the child's segments begin
with the parent's, and the first extra segment is a literal starting with the
path separator. This, and only this, is what makes composition READABLE OFF
THE IRI STRING. -/
def Template.extendedBy (parent child : Template) : Bool :=
  parent.segs.isPrefixOf child.segs
    && (match child.segs.drop parent.segs.length with
        | .lit l :: _ => l.startsWith "/"
        | _ => false)

/-! ## 2. The declaration

What the strings imply is a CANDIDATE order. Which candidate edges are
composition is declared, so that `…/g/{scheme}/c/{concept}` composes into
`…/g/{scheme}` while `…/g/{scheme}/meta/{k}` does not. `composition` holds
pairs of template indices `(parent, child)` and is required to be reflexive
on the declared templates and transitive (`Decl.wf` below). -/
structure Decl where
  templates : List Template
  composition : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- The first template that matches, with its index. Determinism is a
requirement on the declaration (`Decl.deterministic`), not on this function:
the function is total either way, and returns the first match so that a
declaration which violates the requirement still has a defined meaning. -/
def Decl.match? (d : Decl) (iri : String) : Option (Nat × Bindings) :=
  let rec go (i : Nat) : List Template → Option (Nat × Bindings)
    | [] => none
    | t :: ts => match t.match? iri with
        | some b => some (i, b)
        | none => go (i + 1) ts
  go 0 d.templates

/-- Every template of the declaration matches. -/
def Decl.allMatches (d : Decl) (iri : String) : List (Nat × Bindings) :=
  (d.templates.zipIdx).filterMap (fun p =>
    (p.1.match? iri).map (fun b => (p.2, b)))

/-- A template index is a LEAF when no declared composition edge leaves it
downward — nothing composes into it. -/
def Decl.isLeaf (d : Decl) (i : Nat) : Bool :=
  d.composition.all (fun e => !(e.1 == i && e.2 != i))

/-- Well-formedness of a declaration: every template is well formed, the
composition edges point at declared templates, every declared edge is
supported by the string structure (`extendedBy`), the relation is reflexive
on the declared indices and transitive. -/
def Decl.wf (d : Decl) : Bool :=
  let n := d.templates.length
  d.templates.all Template.wf
    && d.composition.all (fun e => decide (e.1 < n) && decide (e.2 < n))
    && d.composition.all (fun e =>
        e.1 == e.2 ||
        (match d.templates[e.1]?, d.templates[e.2]? with
         | some p, some c => Template.extendedBy p c
         | _, _ => false))
    && (List.range n).all (fun i => d.composition.contains (i, i))
    && d.composition.all (fun e =>
        d.composition.all (fun f =>
          !(e.2 == f.1) || d.composition.contains (e.1, f.2)))

/-- The determinism requirement, stated as a `Prop`: an IRI matches at most
one template. A declaration that satisfies it has one leaf per graph IRI,
which is what section 3 of the record calls "unique leaf". -/
def Decl.deterministic (d : Decl) : Prop :=
  ∀ iri : String, (d.allMatches iri).length ≤ 1

/-! ## 3. The composition order over IRI strings

`below d parent child` is the relation the record writes `parent ≤ child`
(the parent is above; the child is one of the graphs whose triples the parent
denotes). Reflexivity on matched IRIs comes from the reflexive edges
`Decl.wf` requires; the string condition is checked as well as the declared
edge, so an IRI that matches a child template but does not extend THIS
parent's instantiation is not below it. -/
def below (d : Decl) (parent child : String) : Bool :=
  match d.match? parent, d.match? child with
  | some (i, _), some (j, _) =>
      d.composition.contains (i, j)
        && parent.toList.isPrefixOf child.toList
  | _, _ => false

/-- The graph names of a dataset that are below `parent`, `parent` itself
included when it names a graph. -/
def leavesOf (d : Decl) (ds : Dataset) (parent : String) : List NamedGraph :=
  ds.named.filter (fun ng =>
    match ng.name with
    | .iri i => below d parent i.val
    | .bnode _ => false)

/-! ## 4. The composed view

The graph a parent IRI denotes: the union of the graphs named by every IRI
below it, its own triples included (it is below itself). `Graph.union`
de-duplicates, so the result is a SET of triples, which RDF 1.1 Concepts
section 3.1 requires of a graph. -/
def view (d : Decl) (ds : Dataset) (parent : String) : Graph :=
  (leavesOf d ds parent).foldl (fun g ng => Graph.union g ng.graph) Graph.empty

/-- The composed dataset: each named graph is replaced by its view. Graphs
whose name is a blank node are carried unchanged — RDF 1.1 Concepts section 4
admits a blank node as a graph name, and no IRI template matches one. -/
def composedDataset (d : Decl) (ds : Dataset) : Dataset :=
  { default := ds.default
  , named := ds.named.map (fun ng =>
      match ng.name with
      | .iri i => { ng with graph := view d ds i.val }
      | .bnode _ => ng) }

/-! ## 5. Splitting a graph by a pattern, and recomposing it -/

/-- Split a graph into named graphs by a key function: one named graph per
distinct key, in first-occurrence order. `none` keeps the triple in the
default graph. This is the packer-side operation the record's per-record and
per-triple cases both use. -/
def splitByKey (key : Triple → Option WfIri) (g : Graph) : Dataset :=
  let step := fun (acc : Dataset) (t : Triple) =>
    match key t with
    | none => { acc with default := Graph.add t acc.default }
    | some name =>
        if acc.named.any (fun ng => ng.name == Subject.iri name) then
          { acc with named := acc.named.map (fun ng =>
              if ng.name == Subject.iri name
              then { ng with graph := Graph.add t ng.graph } else ng) }
        else
          { acc with named := acc.named ++ [{ name := .iri name, graph := [t] }] }
  g.foldl step Dataset.empty

/-- The union of every graph of a dataset. -/
def recompose (ds : Dataset) : Graph :=
  ds.named.foldl (fun g ng => Graph.union g ng.graph) ds.default

/-! ## 6. Per-triple graph names

A per-triple pattern names each one-triple graph from the triple's own
canonical form — RDFC-1.0 over the single-triple graph, then a hash. The
naming function is a parameter here: `RDF/Canonical.lean` holds the
canonicalization and this module must not depend on it. -/
def perTripleName (base : String) (canon : Triple → String) (t : Triple) : String :=
  base ++ canon t

/-! ## 7. Theorem statements

Definitional facts are proved. Everything else is a `Prop`-valued `def`,
which is a statement without a proof and without a `sorry`. -/

/-- The view is the union of the graphs below the parent. Definitional. -/
theorem view_eq_union (d : Decl) (ds : Dataset) (parent : String) :
    view d ds parent
      = (leavesOf d ds parent).foldl (fun g ng => Graph.union g ng.graph)
          Graph.empty := rfl

/-- A graph below the parent contributes its name to the leaf list.
Definitional. -/
theorem mem_leavesOf (d : Decl) (ds : Dataset) (parent : String)
    (ng : NamedGraph) :
    ng ∈ leavesOf d ds parent ↔
      (ng ∈ ds.named ∧
        (match ng.name with
         | .iri i => below d parent i.val
         | .bnode _ => false) = true) := by
  simp [leavesOf, List.mem_filter]

/-- The composed dataset keeps the default graph. Definitional. -/
theorem composed_default (d : Decl) (ds : Dataset) :
    (composedDataset d ds).default = ds.default := rfl

/-- The composed dataset names exactly the graphs the source names.
Definitional. -/
theorem composed_names (d : Decl) (ds : Dataset) :
    (composedDataset d ds).named.map NamedGraph.name
      = ds.named.map NamedGraph.name := by
  have general : ∀ (l : List NamedGraph),
      (l.map (fun ng =>
        match ng.name with
        | .iri i => { ng with graph := view d ds i.val }
        | .bnode _ => ng)).map NamedGraph.name = l.map NamedGraph.name := by
    intro l
    induction l with
    | nil => rfl
    | cons ng rest ih =>
        simp only [List.map_cons, ih]
        cases ng with
        | mk name graph => cases name <;> rfl
  exact general ds.named

/-- **T1 — partial order.** On the IRIs a well-formed, deterministic
declaration matches, `below` is reflexive, antisymmetric and transitive. -/
def IsPartialOrder (d : Decl) : Prop :=
  d.wf = true → d.deterministic →
    (∀ g, (d.match? g).isSome → below d g g = true) ∧
    (∀ g h, below d g h = true → below d h g = true → g = h) ∧
    (∀ g h k, below d g h = true → below d h k = true → below d g k = true)

/-- **T2 — unique leaf.** A deterministic declaration gives every graph IRI at
most one matching template, so a triple placed by the pattern lands in exactly
one leaf graph. -/
def UniqueLeaf (d : Decl) : Prop :=
  d.deterministic →
    ∀ iri i j bi bj,
      (i, bi) ∈ d.allMatches iri → (j, bj) ∈ d.allMatches iri → i = j ∧ bi = bj

/-- **T3 — monotone in the leaf set.** Adding a named graph to the dataset
only adds triples to a view. -/
def ViewMonotone (d : Decl) : Prop :=
  ∀ (ds : Dataset) (ng : NamedGraph) (parent : String) (t : Triple),
    Graph.mem t (view d ds parent) = true →
    Graph.mem t (view d { ds with named := ds.named ++ [ng] } parent) = true

/-- **T4 — query equivalence for a constant parent graph.** For any function
of a graph — a basic graph pattern's solutions, an ASK, a CONSTRUCT — the
answer over the view of the parent equals the answer over the union of the
graphs the pattern puts below it. This is the shape the planner's graph
collector needs: `queryGraphNames?` maps a constant `GRAPH <parent>` to the
LEAF SET, and the answer must not change.

Stated over an abstract `eval` so that this module does not import
`SPARQL/Query.lean`; the record names the concrete instance. -/
def ConstantParentEquivalence (d : Decl) : Prop :=
  ∀ {Answer : Type} (eval : Graph → Answer) (ds : Dataset) (parent : String),
    eval (view d ds parent) = eval (recompose { ds with
      default := Graph.empty, named := leavesOf d ds parent })

/-- **T5 — content determines the name.** With an injective canonical form,
a per-triple graph name determines the triple, so retracting a graph BY NAME
retracts exactly the triple with that content. -/
def PerTripleDetermined (base : String) (canon : Triple → String) : Prop :=
  (∀ t u, canon t = canon u → t = u) →
    ∀ t u, perTripleName base canon t = perTripleName base canon u → t = u

/-- **T6 — split then recompose.** Splitting a graph by any key function and
taking the union of the pieces gives back the graph as a SET of triples. -/
def SplitRoundTrip : Prop :=
  ∀ (key : Triple → Option WfIri) (g : Graph) (t : Triple),
    Graph.mem t g = Graph.mem t (recompose (splitByKey key g))

/-! ## 8. A worked declaration — the skosdex shape

`https://skosdex.example/g/{scheme}` with
`https://skosdex.example/g/{scheme}/c/{concept}` below it, and
`https://skosdex.example/g/{scheme}/meta/{key}` NOT below it: the third
template is declared with no edge into template 0. -/
def schemeTemplate : Template :=
  { segs := [.lit "https://skosdex.example/g/", .var "scheme"] }

def conceptTemplate : Template :=
  { segs := [.lit "https://skosdex.example/g/", .var "scheme",
             .lit "/c/", .var "concept"] }

def metaTemplate : Template :=
  { segs := [.lit "https://skosdex.example/g/", .var "scheme",
             .lit "/meta/", .var "key"] }

def skosdexTemplates : List Template :=
  [schemeTemplate, conceptTemplate, metaTemplate]

def skosdexDecl : Decl :=
  { templates := skosdexTemplates
  , composition := [(0, 0), (1, 1), (2, 2), (0, 1)] }

/-! ### Build-time checks -/

#guard skosdexTemplates.all Template.wf
#guard skosdexDecl.wf
#guard Template.extendedBy schemeTemplate conceptTemplate
#guard Template.extendedBy schemeTemplate metaTemplate

-- Matching is by template, and the concept template binds both variables.
#guard schemeTemplate.match? "https://skosdex.example/g/unesco"
  == some [("scheme", "unesco")]
#guard conceptTemplate.match? "https://skosdex.example/g/unesco/c/C1234"
  == some [("scheme", "unesco"), ("concept", "C1234")]
#guard schemeTemplate.match? "https://skosdex.example/g/unesco/c/C1234"
  == none

-- A concept graph is below its scheme graph; a meta graph is not, because no
-- composition edge was declared for it even though the string extends.
#guard below skosdexDecl "https://skosdex.example/g/unesco"
  "https://skosdex.example/g/unesco/c/C1234"
#guard !(below skosdexDecl "https://skosdex.example/g/unesco"
  "https://skosdex.example/g/unesco/meta/dcterms")
-- and not below a DIFFERENT scheme's graph.
#guard !(below skosdexDecl "https://skosdex.example/g/unesco"
  "https://skosdex.example/g/gemet/c/C1234")
-- Reflexive on a matched IRI.
#guard below skosdexDecl "https://skosdex.example/g/unesco"
  "https://skosdex.example/g/unesco"

-- Expansion is the inverse of matching on a matched IRI (RFC 6570 level 1).
#guard conceptTemplate.expand? [("scheme", "unesco"), ("concept", "C1234")]
  == some "https://skosdex.example/g/unesco/c/C1234"

end L4Factoidal.RDF.GraphPatterns
