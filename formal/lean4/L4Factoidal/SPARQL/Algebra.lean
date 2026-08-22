/-
L4Factoidal.SPARQL.Algebra — solution mappings, triple patterns, BGP
matching, and the core SPARQL 1.1 algebra (§18.5).

Port of the corresponding sections of
`formal/fstar/SPARQL11.Algebra.fst`:
  * Part 1 solution-mapping operations (`sm_*`);
  * Part 2 pattern terms / triple patterns (including SPARQL 1.2
    triple-term patterns, epic #305);
  * §7.2 BGP evaluation (`try_bind_*`, `tp_match`, `eval_bgp`);
  * §7.3/§18.5 algebra operations (`join`, `left_join`, `union`,
    `minus`, filter).

What is deliberately NOT ported here (with why):
  * the `graph_store`/`RDF.Indexed` seam, index-driven candidate
    search, the `choose_best_tp` selectivity planner, and the keyed
    hash join — engine PERFORMANCE machinery. This file is the
    SPECIFICATION-level evaluator: `evalTP` scans the graph list, the
    BGP evaluator takes patterns left-to-right, `join` is the
    nested-loop compatible-merge. (The F* source's own banner frames
    the hash join as an optimisation over exactly this semantics.)
  * the SPARQL expression language (`expr`, `eval_expr`, effective
    boolean value). `Filter`/`LeftJoin` conditions are abstracted as
    `Binding → Bool` — the shape §18.5 needs from a filter. The
    expression AST is a later porting stage of its own.
  * property paths, GRAPH/SERVICE/VALUES/BIND/sub-SELECT — the wider
    `GraphPattern` constructor set beyond this port's step-2 scope.

Readability contract: every definition cites the SPARQL 1.1 spec
section it implements; names track the spec's vocabulary (solution
mapping, compatibility, merge) rather than implementation jargon.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Solution mappings — SPARQL 1.1 §18.1.8

"A solution mapping μ is a partial function from query variables to
RDF terms." Represented as an association list; earlier entries
shadow later ones (matching the F* representation exactly). -/

abbrev VarName := String

/-- A solution mapping (also called a binding row). -/
abbrev Binding := List (VarName × Term)

/-- A solution sequence: the result of evaluating a graph pattern. -/
abbrev SolutionSeq := List Binding

def Binding.empty : Binding := []

/-- μ(v) — port of `sm_lookup`. -/
def Binding.lookup (v : VarName) : Binding → Option Term
  | []             => none
  | (w, t) :: rest => if w = v then some t else Binding.lookup v rest

/-- Extend μ with v ↦ t (no shadow check; callers check first) —
port of `sm_bind`. -/
def Binding.bind (v : VarName) (t : Term) (mu : Binding) : Binding :=
  (v, t) :: mu

/-- dom(μ) — port of `sm_domain`. -/
def Binding.domain (mu : Binding) : List VarName :=
  mu.map Prod.fst

/-- SPARQL 1.1 §18.3: "Two solution mappings μ1 and μ2 are compatible
if, for every variable v in dom(μ1) and in dom(μ2), μ1(v) = μ2(v)."
Term comparison is the engine equality `Term.eqb` (language-tag case,
XMLLiteral c14n) — port of `sm_compatible`. -/
def Binding.compatible : Binding → Binding → Bool
  | [],             _   => true
  | (v, t) :: rest, mu2 =>
      (match mu2.lookup v with
       | none    => true
       | some t2 => t.eqb t2) && Binding.compatible rest mu2

/-- merge(μ1, μ2): μ1's bindings take priority; μ2's non-overlapping
bindings are added — port of `sm_merge`/`sm_merge_aux` (including its
accumulate-by-cons order). Callers guard with `compatible`. -/
def Binding.merge (mu1 : Binding) : Binding → Binding
  | []             => mu1
  | (v, t) :: rest =>
      match mu1.lookup v with
      | some _ => Binding.merge mu1 rest
      | none   => Binding.merge ((v, t) :: mu1) rest

/-! ## Pattern terms and triple patterns — SPARQL 1.1 §18.1.6/§18.2

SPARQL 1.2 (epic #305): `PatternTerm.tripleTerm` is a triple-term
pattern `<<( s p o )>>` whose sub-positions are themselves pattern
terms; `PatternSubject.tripleTerm` is the same shape in subject
position — matchable against no concrete data subject, which is the
RDF 1.2 "triple terms are object-only" rule surfacing at match
time. -/

inductive PatternTerm where
  | var        (v : VarName)
  | iri        (i : WfIri)
  | bnode      (b : BNodeId)
  | literal    (l : WfLiteral)
  | tripleTerm (s p o : PatternTerm)
  deriving Repr

inductive PatternSubject where
  | var        (v : VarName)
  | iri        (i : WfIri)
  | bnode      (b : BNodeId)
  | tripleTerm (s p o : PatternTerm)
  deriving Repr

/-- A triple pattern: subject, predicate, object — SPARQL 1.1 allows
a variable in any position (§18.1.6). -/
structure TriplePattern where
  s : PatternSubject
  p : PatternTerm
  o : PatternTerm
  deriving Repr

/-- A Basic Graph Pattern (§18.1.7): a list of triple patterns. -/
abbrev Bgp := List TriplePattern

/-! ## Matching — §18.3.1, one triple at a time

`tryBindSubject`/`tryBindTerm` attempt to match one pattern position
against one concrete position under a partial solution mapping,
extending the mapping on success. Bindings thread subject →
predicate → object, exactly as in the F* source. -/

/-- Port of `try_bind_subject`. -/
def tryBindSubject (ps : PatternSubject) (s : Subject) (mu : Binding) :
    Option Binding :=
  match ps with
  | .iri i =>
      match s with
      | .iri i' => if i == i' then some mu else none
      | _       => none
  | .bnode b =>
      match s with
      | .bnode b' => if b == b' then some mu else none
      | _         => none
  -- A triple-term subject pattern never matches a concrete data
  -- subject (data subjects are IRI/bnode only).
  | .tripleTerm _ _ _ => none
  | .var v =>
      let term := s.toTerm
      match mu.lookup v with
      | some existing => if existing.eqb term then some mu else none
      | none          => some (mu.bind v term)

/-- Port of `try_bind_term`. RDF 1.2: a triple-term pattern matches a
concrete `Term.tripleTerm` by recursively binding its three
sub-positions. -/
def tryBindTerm : PatternTerm → Term → Binding → Option Binding
  | .iri i, t, mu =>
      match t with
      | .iri i' => if i == i' then some mu else none
      | _       => none
  | .bnode b, t, mu =>
      match t with
      | .bnode b' => if b == b' then some mu else none
      | _         => none
  | .literal l, t, mu =>
      match t with
      | .literal l' => if l.val.eqb l'.val then some mu else none
      | _           => none
  | .tripleTerm ps pp po, t, mu =>
      match t with
      | .tripleTerm s p o =>
          match tryBindTerm ps s.toTerm mu with
          | none     => none
          | some mu1 =>
              match tryBindTerm pp (.iri p) mu1 with
              | none     => none
              | some mu2 => tryBindTerm po o mu2
      | _ => none
  | .var v, t, mu =>
      match mu.lookup v with
      | some existing => if existing.eqb t then some mu else none
      | none          => some (mu.bind v t)

/-- Match one triple pattern against one graph triple under μ,
producing the extended mapping — port of `tp_match`. -/
def tpMatch (tp : TriplePattern) (t : Triple) (mu : Binding) :
    Option Binding :=
  match tryBindSubject tp.s t.s mu with
  | none     => none
  | some mu1 =>
      match tryBindTerm tp.p (.iri t.p) mu1 with
      | none     => none
      | some mu2 => tryBindTerm tp.o t.o mu2

/-! ## BGP evaluation — §18.3 / F* §7.2

Specification-level: one triple pattern extends each current row by
scanning the whole graph (`List.filterMap`); a BGP is the
left-to-right sequential extension. (The F* executable additionally
reorders patterns by index selectivity — `choose_best_tp` — and
probes indexes; that changes cost, not the result set.) -/

/-- All extensions of μ by matching `tp` somewhere in `g`. -/
def evalTP (tp : TriplePattern) (g : Graph) (mu : Binding) : SolutionSeq :=
  g.filterMap (fun t => tpMatch tp t mu)

/-- Sequential BGP evaluation from a seed mapping. -/
def evalBgpFrom (g : Graph) : Bgp → Binding → SolutionSeq
  | [],         mu => [mu]
  | tp :: rest, mu => (evalTP tp g mu).flatMap (evalBgpFrom g rest)

/-- eval(BGP) — §18.3: the empty BGP yields exactly the empty
mapping; otherwise each pattern extends the rows of the previous
ones. -/
def evalBgp (b : Bgp) (g : Graph) : SolutionSeq :=
  evalBgpFrom g b Binding.empty

/-! ## Core algebra operations — §18.5 -/

/-- Join(Ω1, Ω2) = { merge(μ1, μ2) | μ1 ∈ Ω1, μ2 ∈ Ω2, compatible } —
the specification nested-loop form (the F* engine's keyed hash join
computes the same set). -/
def join (omega1 omega2 : SolutionSeq) : SolutionSeq :=
  omega1.flatMap (fun mu1 =>
    omega2.filterMap (fun mu2 =>
      if mu1.compatible mu2 then some (mu1.merge mu2) else none))

/-- Union(Ω1, Ω2): multiset union — port of `union`. -/
def union (omega1 omega2 : SolutionSeq) : SolutionSeq :=
  omega1 ++ omega2

/-- dom(μ1) ∩ dom(μ2) = ∅ — port of `domains_disjoint`. -/
def domainsDisjoint : Binding → Binding → Bool
  | [],             _   => true
  | (v, _) :: rest, mu2 =>
      (mu2.lookup v).isNone && domainsDisjoint rest mu2

/-- Minus(Ω1, Ω2) = { μ1 ∈ Ω1 | ∀ μ2 ∈ Ω2 :
¬compatible(μ1, μ2) ∨ dom(μ1) ∩ dom(μ2) = ∅ } — §18.5, port of
`minus`. -/
def minus (omega1 omega2 : SolutionSeq) : SolutionSeq :=
  omega1.filter (fun mu1 =>
    !omega2.any (fun mu2 =>
      mu1.compatible mu2 && !domainsDisjoint mu1 mu2))

/-- Filter(expr, Ω) with the condition abstracted as a predicate on
rows (see the module banner for why the expression AST is not in this
stage). -/
def filterSeq (cond : Binding → Bool) (omega : SolutionSeq) : SolutionSeq :=
  omega.filter cond

/-- LeftJoin(Ω1, Ω2, expr) — §18.5: for each μ1, the
condition-passing compatible merges if any exist, else μ1 itself
(kept unextended). Equivalent to the spec's
`Filter(expr, Join) ∪ Diff(Ω1, Ω2, expr)` formulation, grouped by
left row. -/
def leftJoin (omega1 omega2 : SolutionSeq) (cond : Binding → Bool) :
    SolutionSeq :=
  omega1.flatMap (fun mu1 =>
    let extended := omega2.filterMap (fun mu2 =>
      if mu1.compatible mu2 then
        let merged := mu1.merge mu2
        if cond merged then some merged else none
      else none)
    if extended.isEmpty then [mu1] else extended)

/-! ## Graph patterns — the algebra AST (§18.2.2.6 output forms)

The constructor set of this stage: BGP and the §18.5 binary
operations. (The full F* `group_graph_pattern` additionally carries
GRAPH, SERVICE, BIND, VALUES, sub-SELECT, property paths, and the
SPARQL 1.2-track LATERAL — later porting stages.) -/

inductive GraphPattern where
  | bgp      (patterns : Bgp)
  | join     (l r : GraphPattern)
  | leftJoin (l r : GraphPattern) (cond : Binding → Bool)
  | filter   (cond : Binding → Bool) (p : GraphPattern)
  | union    (l r : GraphPattern)
  | minus    (l r : GraphPattern)

/-- eval(P, G) — §18.5's recursive evaluation over the algebra. -/
def GraphPattern.eval (g : Graph) : GraphPattern → SolutionSeq
  | .bgp b           => evalBgp b g
  | .join l r        => SPARQL.join (l.eval g) (r.eval g)
  | .leftJoin l r c  => SPARQL.leftJoin (l.eval g) (r.eval g) c
  | .filter c p      => filterSeq c (p.eval g)
  | .union l r       => SPARQL.union (l.eval g) (r.eval g)
  | .minus l r       => SPARQL.minus (l.eval g) (r.eval g)

end L4Factoidal.SPARQL
