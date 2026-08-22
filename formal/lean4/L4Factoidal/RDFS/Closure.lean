/-
L4Factoidal.RDFS.Closure — the EXECUTABLE rho-df closure.

Port of the extractable part of
`formal/fstar/RDF.Entailment.RDFS.RhoDFClosure.fst`:
`rho_df_closure_step_pre_dedup` (line 98), `rho_df_closure_step`
(line 107) and the fuel/length-test fixpoint `rho_df_closure`
(line 114), together with the six `rdfs_rule_*` bodies those compose,
which live in `formal/fstar/RDFS.Closure.fsti` lines 242-355.

`RhoDF.lean` is the specification (the rule relation `Derives`); this
file is the implementation; `ClosureTheorems.lean` connects them. The
split is deliberate: a reviewer checks the six inductive constructors
of `Derives` against the RDF 1.1 Semantics §9.2 table by eye, and
trusts this file only through the proved theorems.

## Two faithful-port decisions, and one deliberate deviation

1. **Deduplication is `Graph.add`'s**, i.e. the engine's `Triple.eqb`
   membership — the same set semantics `RDF.Graph`'s `graph_add` has.
   The F* step ends in `graph_dedup_sort`; sorting is a performance
   device (it makes the length test cheap and the index build linear)
   and carries no semantics, so it is not ported. What IS ported is
   that the step emits no duplicate: `addAll` folds `Graph.add`.

2. **The fixpoint test is the F* one**: run a step, compare LENGTHS,
   stop when the length did not move. `addAll_eq_of_length_eq` in
   `ClosureTheorems.lean` proves that test exact for this step
   function — equal length really does imply the step was the
   identity — which the F* module carries as the hypothesis pair
   `no_repeats_p g` / `no_repeats_p (rho_df_closure_step g)` on
   `lemma_len_eq_saturated` rather than discharging.

3. **DEVIATION (documented, semantics-preserving at the fixpoint).**
   The F* step threads its accumulator through the six rows, so a
   triple emitted by rdfs7 inside a step can drive rdfs9 in the SAME
   step (the rows read premises from the snapshot index `ig`, but
   rdfs9/rdfs11/rdfs5 fold over the accumulated graph). This port
   reads EVERY premise from the step's input snapshot `g`. Per step
   this can emit less; at the fixpoint it emits the same set, since a
   conclusion the F* step reaches through an intra-step chain is
   reached here one round later, and the loop runs to saturation.
   The cost is iteration count, not the result. Stated this way the
   step is a plain function of its input, which is what makes the
   soundness and saturation proofs one induction each.
-/
import L4Factoidal.RDFS.RhoDF

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## Premise lookup

The F* rows read premises through `build_indexed`'s buckets
(`bucket_lookup ig.ig_pred p`, `find_objects_indexed ig s p`). The
index is performance machinery; the specification-level lookup is a
list scan with the same answer. -/

/-- Every object of a `(s, p, ·)` triple of `g` — the specification
counterpart of `find_objects_indexed ig s p`. -/
def objectsOf (g : Graph) (s : Subject) (p : WfIri) : List Term :=
  (g.filter (fun t => t.s == s && t.p == p)).map (fun t => t.o)

/-- Every triple of `g` with predicate `p` — the specification
counterpart of `bucket_lookup ig.ig_pred p`. -/
def triplesWithPredicate (g : Graph) (p : WfIri) : List Triple :=
  g.filter (fun t => t.p == p)

/-! ## The six rows

Each `rdfsNFor g t` reads `t` as the row's FIRST premise and returns
every conclusion that row licenses from `t` together with a second
premise found in `g`. Rows rdfs7/rdfs2/rdfs3 are driven by the schema
declaration (the join reorder of F* task #36); rows rdfs9/rdfs11/rdfs5
are driven by the data triple, exactly as the F* bodies are. -/

/-- **rdfs7** (`rdfs_rule_subPropertyOf`): from a declaration
`p rdfs:subPropertyOf q`, re-assert every `p`-triple of `g` under
`q`. -/
def rdfs7For (g : Graph) (decl : Triple) : List Triple :=
  match decl.s, decl.o with
  | .iri p, .iri q =>
      if decl.p == rdfsSubPropertyOf then
        (triplesWithPredicate g p).map (fun t => ⟨t.s, q, t.o⟩)
      else []
  | _, _ => []

/-- **rdfs2** (`rdfs_rule_domain`): from `p rdfs:domain C`, type the
subject of every `p`-triple of `g` as a `C`. -/
def rdfs2For (g : Graph) (decl : Triple) : List Triple :=
  match decl.s with
  | .iri p =>
      if decl.p == rdfsDomain then
        (triplesWithPredicate g p).map (fun t => ⟨t.s, rdfType, decl.o⟩)
      else []
  | _ => []

/-- **rdfs3** (`rdfs_rule_range`): from `p rdfs:range C`, type the
object of every `p`-triple of `g` as a `C` — skipping the triples
whose object cannot be a subject (literals, and RDF 1.2 triple
terms). -/
def rdfs3For (g : Graph) (decl : Triple) : List Triple :=
  match decl.s with
  | .iri p =>
      if decl.p == rdfsRange then
        (triplesWithPredicate g p).filterMap (fun t =>
          match t.o.toSubject? with
          | some osub => some ⟨osub, rdfType, decl.o⟩
          | none      => none)
      else []
  | _ => []

/-- **rdfs9** (`rdfs_rule_subClassOf`): from a data triple
`s rdf:type A`, re-type `s` under every super-class of `A` in `g`. -/
def rdfs9For (g : Graph) (t : Triple) : List Triple :=
  match t.o with
  | .iri a =>
      if t.p == rdfType then
        (objectsOf g (Subject.iri a) rdfsSubClassOf).map
          (fun b => ⟨t.s, rdfType, b⟩)
      else []
  | _ => []

/-- **rdfs11** (`rdfs_rule_subClassOf_trans`): from `A rdfs:subClassOf
B`, compose with every `B rdfs:subClassOf C` of `g`. -/
def rdfs11For (g : Graph) (t : Triple) : List Triple :=
  if t.p == rdfsSubClassOf then
    match t.o.toSubject? with
    | some bsub =>
        (objectsOf g bsub rdfsSubClassOf).map
          (fun c => ⟨t.s, rdfsSubClassOf, c⟩)
    | none => []
  else []

/-- **rdfs5** (`rdfs_rule_subPropertyOf_trans`): the dual of rdfs11
for the property hierarchy. -/
def rdfs5For (g : Graph) (t : Triple) : List Triple :=
  if t.p == rdfsSubPropertyOf then
    match t.o.toSubject? with
    | some bsub =>
        (objectsOf g bsub rdfsSubPropertyOf).map
          (fun c => ⟨t.s, rdfsSubPropertyOf, c⟩)
    | none => []
  else []

/-! ## One step -/

/-- Everything the six rows conclude from `g` in one round, before
deduplication — the counterpart of
`rho_df_closure_step_pre_dedup`, in the same row order (rdfs7,
rdfs2, rdfs3, rdfs9, rdfs11, rdfs5). Unlike the F* function this
returns only the NEW conclusions, not `g` extended by them; `step`
adds them. -/
def stepConclusions (g : Graph) : List Triple :=
  g.flatMap (rdfs7For g) ++
  g.flatMap (rdfs2For g) ++
  g.flatMap (rdfs3For g) ++
  g.flatMap (rdfs9For g) ++
  g.flatMap (rdfs11For g) ++
  g.flatMap (rdfs5For g)

/-- Add a list of triples set-wise (`Graph.add` skips a triple the
graph already holds under `Triple.eqb`). -/
def addAll (g : Graph) : List Triple → Graph
  | []      => g
  | t :: ts => addAll (g.add t) ts

/-- One closure round: `g` plus every conclusion the six rows license
from `g`, deduplicated — port of `rho_df_closure_step`. -/
def step (g : Graph) : Graph :=
  addAll g (stepConclusions g)

/-! ## The fixpoint loop -/

/-- Fuel-bounded fixpoint — port of `rho_df_closure` (line 114),
including its exact stopping rule: run a step, and if the LENGTH did
not change, return the INPUT `g` (not the step's output; at equal
length the two hold the same triples — see
`ClosureTheorems.addAll_eq_of_length_eq`). -/
def closure (g : Graph) (fuel : Nat) : Graph :=
  match fuel with
  | 0     => g
  | n + 1 =>
      let g' := step g
      if g'.length = g.length then g else closure g' n

/-- Repeated stepping with no fixpoint test — port of
`rho_df_closure_iter` (line 124). Used by the theorems, not by
callers. -/
def closureIter (g : Graph) : Nat → Graph
  | 0     => g
  | n + 1 => closureIter (step g) n

/-- The fuel budget `closureFix` spends.

The F* module leaves fuel to the caller, and the F* tree's callers
pass the constant 100 (`bin/w3c-runner/w3c_runner.ml:1276`,
`bin/factoidal-cli/factoidal_cli.ml:2427`) — a resource budget, not a
bound with an argument behind it. The bound here has the counting
argument behind it instead:

* the loop only recurses when the step STRICTLY grew the graph (equal
  length stops it), so at most one iteration per triple ever added;
* every rule conclusion is built from components already present —
  its subject is a subject or object of `g`, its object is an object
  of `g`, and its predicate is a predicate of `g` or `rdf:type` — so
  the closure of an `n`-triple graph holds at most `n * (n + 1) * n`
  triples;

hence `n * (n + 1) * n + 1` rounds cannot be exhausted before the
length test fires. The counting argument is stated, NOT proved:
`ClosureTheorems.closure_saturated_or_underfueled` is what is proved,
and it says precisely that the only alternative to saturation is a
closure that grew by at least one triple per unit of fuel. Formalising
the term-universe bound is the named remaining obligation. -/
def closureFuelBound (g : Graph) : Nat :=
  g.length * (g.length + 1) * g.length + 1

/-- The closure at the fuel bound above. -/
def closureFix (g : Graph) : Graph :=
  closure g (closureFuelBound g)

end L4Factoidal.RDFS
