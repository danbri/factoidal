/-
L4Factoidal.RDF.Graph — graphs, datasets, and graph operations.

Port of `formal/fstar/RDF.Graph.fsti` to Lean 4, plus the blank-node
renaming operation from `RDF.Dataset.Merge` that per-document
blank-node scoping needs.

An RDF graph is a SET of triples (RDF 1.1 Concepts §3). Like the F*
source, the representation is a `List Triple` so evaluation executes
directly, with set semantics maintained by the operations
(`Graph.mem` via the engine triple equality, `Graph.add`'s
deduplication) rather than by the representation type. A
`Finset`-based purely-specification twin is a candidate later layer;
this file is the executable one, matching the F* module it ports.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.RDF

/-! ## Graphs — RDF 1.1 Concepts §3 ("a set of RDF triples") -/

/-- An RDF graph: a list of triples with set semantics maintained by
the operations below. -/
abbrev Graph := List Triple

def Graph.empty : Graph := []

/-- Membership via the engine triple equality `Triple.eqb` (literal
comparison goes through the language-tag / XMLLiteral rules, not raw
record equality) — port of `mem_triple`. -/
def Graph.mem (t : Triple) : Graph → Bool
  | []       => false
  | hd :: tl => hd.eqb t || Graph.mem t tl

/-- Set-based add: only add if not already present — port of
`graph_add`. -/
def Graph.add (t : Triple) (g : Graph) : Graph :=
  if g.mem t then g else g ++ [t]

/-- Remove every occurrence of `t`, by the same engine equality
`Graph.mem` and `Graph.add` use — port of `graph_remove`. -/
def Graph.remove (t : Triple) (g : Graph) : Graph :=
  g.filter (fun u => !u.eqb t)

/-- Graph union with deduplication: every triple of `g2` added to
`g1` set-wise. -/
def Graph.union (g1 g2 : Graph) : Graph :=
  g2.foldl (fun acc t => acc.add t) g1

/-! ## Blank-node renaming

RDF 1.1 Concepts §3.4: blank-node labels are document-scoped, so
merging graphs from separate documents must first rename each
document's labels apart (this is what makes graph MERGE different
from graph union). `renameBnodes f` applies a label mapping
everywhere a blank node can occur — including inside RDF 1.2 triple
terms. -/

def Subject.renameBnodes (f : BNodeId → BNodeId) : Subject → Subject
  | .iri i   => .iri i
  | .bnode b => .bnode (f b)

def Term.renameBnodes (f : BNodeId → BNodeId) : Term → Term
  | .iri i            => .iri i
  | .bnode b          => .bnode (f b)
  | .literal l        => .literal l
  | .tripleTerm s p o => .tripleTerm (s.renameBnodes f) p (o.renameBnodes f)

def Triple.renameBnodes (f : BNodeId → BNodeId) (t : Triple) : Triple :=
  { s := t.s.renameBnodes f, p := t.p, o := t.o.renameBnodes f }

def Graph.renameBnodes (f : BNodeId → BNodeId) (g : Graph) : Graph :=
  g.map (Triple.renameBnodes f)

/-- Prefix every blank-node label — the concrete renaming
`RDF.Dataset.Merge.rename_dataset_bnodes` uses to scope one parsed
document's labels apart from every other's. Injective for any prefix,
so distinct labels stay distinct. -/
def Graph.prefixBnodes (pre : String) (g : Graph) : Graph :=
  g.renameBnodes (fun b => pre ++ b)

/-! ## Datasets — RDF 1.1 Concepts §4 -/

/-- One named graph. RDF 1.1 Concepts §4 says a graph name "may be an
IRI or a blank node", so the name slot is a `Subject` — the sum of
exactly those two — and not an `Iri` string. That is what the N-Quads
`[6] graphLabel` and TriG `[7g] labelOrSubject` productions accept, so
the parsers hand the label straight over with no encoding in between.
(The F* source's `named_graph.ng_name` is a bare `iri`, which is why
`RDF.NQuads` there packs a blank-node name into the string as
`"_:label"`; this port carries the sum type instead.) -/
structure NamedGraph where
  name  : Subject
  graph : Graph
  deriving DecidableEq, Repr

/-- An RDF dataset: exactly one default graph plus zero or more named
graphs — the unit SPARQL's `FROM`/`FROM NAMED`/`GRAPH` clauses
(SPARQL 1.1 §13.2) query against. -/
structure Dataset where
  default : Graph
  named   : List NamedGraph
  deriving DecidableEq, Repr

def Dataset.empty : Dataset := { default := [], named := [] }

/-- Look up a named graph by its name — an IRI or a blank node (port of
`lookup_named_graph`). -/
def Dataset.lookupNamed (name : Subject) (ds : Dataset) : Option Graph :=
  match ds.named.find? (fun ng => ng.name == name) with
  | some ng => some ng.graph
  | none    => none

/-- Look up a named graph by a plain IRI — the SPARQL 1.1 `GRAPH <iri>`
(§13.3) and `FROM NAMED` (§13.2) call sites, where the grammar admits
only an IRI in the name position. A string that is not a well-formed
IRI names nothing. -/
def Dataset.lookupNamedIri (i : Iri) (ds : Dataset) : Option Graph :=
  if h : isIri i = true then ds.lookupNamed (.iri ⟨i, h⟩) else none

/-! ## Blank-node renaming over a dataset

RDF 1.1 Concepts §3.4 scopes blank-node labels to the whole document,
and §4 puts graph NAMES in that scope too — a `_:g` used as a graph
name is the same blank node as a `_:g` in a triple. So a dataset-wide
renaming touches the name slot as well as the triples. -/

/-- Rename every blank node of a dataset: default graph, every named
graph, and every blank-node graph NAME. -/
def Dataset.renameBnodes (f : BNodeId → BNodeId) (ds : Dataset) : Dataset :=
  { default := ds.default.renameBnodes f,
    named   := ds.named.map (fun ng =>
      { name := ng.name.renameBnodes f, graph := ng.graph.renameBnodes f }) }

/-- Prefix every blank-node label of a dataset — the dataset-wide
counterpart of `Graph.prefixBnodes`, used to scope one parsed
document's labels apart from another's. -/
def Dataset.prefixBnodes (pre : String) (ds : Dataset) : Dataset :=
  ds.renameBnodes (fun b => pre ++ b)

/-! ## Set-semantics theorems -/

/-- Membership distributes over append. -/
theorem Graph.mem_append (g1 g2 : Graph) (u : Triple) :
    Graph.mem u (g1 ++ g2) = (Graph.mem u g1 || Graph.mem u g2) := by
  induction g1 with
  | nil => simp [Graph.mem]
  | cons hd tl ih => simp [Graph.mem, ih, Bool.or_assoc]

/-- `add` never loses membership. -/
theorem Graph.mem_add_of_mem (g : Graph) (t u : Triple)
    (h : g.mem u = true) : (g.add t).mem u = true := by
  unfold Graph.add
  by_cases hm : g.mem t = true <;> simp [hm, Graph.mem_append, h]

/-- The added triple is a member of the result (via `Triple.eqb`
reflexivity). -/
theorem Graph.mem_add_self (g : Graph) (t : Triple) :
    (g.add t).mem t = true := by
  unfold Graph.add
  by_cases hm : g.mem t = true <;> simp [hm, Graph.mem_append, Graph.mem]

/-! ## List membership vs engine membership; `add` and length

Harvested 2026-08-22 from the rdfs-core closure proofs. -/

/-- List membership implies engine membership (`Triple.eqb` is
reflexive). -/
theorem graphMem_of_mem {g : Graph} {t : Triple} (h : t ∈ g) :
    Graph.mem t g = true := by
  induction g with
  | nil => cases h
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [Graph.mem]
    · simp [Graph.mem, ih h']

/-- Engine membership is witnessed by an eqb-equal list element. -/
theorem exists_of_graphMem {g : Graph} {t : Triple}
    (h : Graph.mem t g = true) : ∃ u, u ∈ g ∧ Triple.eqb u t = true := by
  induction g with
  | nil => simp [Graph.mem] at h
  | cons hd tl ih =>
    simp only [Graph.mem, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨hd, List.mem_cons_self .., h⟩
    · obtain ⟨u, hu, he⟩ := ih h
      exact ⟨u, List.mem_cons_of_mem _ hu, he⟩

theorem mem_add_of_mem_list {g : Graph} {t u : Triple} (h : t ∈ g) :
    t ∈ g.add u := by
  unfold Graph.add
  split
  · exact h
  · exact List.mem_append_left _ h

theorem mem_add_cases {g : Graph} {t u : Triple} (h : t ∈ g.add u) :
    t ∈ g ∨ t = u := by
  unfold Graph.add at h
  split at h
  · exact Or.inl h
  · rcases List.mem_append.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (List.mem_singleton.mp h')

theorem length_le_add (g : Graph) (u : Triple) :
    g.length ≤ (g.add u).length := by
  unfold Graph.add
  split
  · exact Nat.le_refl _
  · simp

theorem add_eq_of_length_eq {g : Graph} {u : Triple}
    (h : (g.add u).length = g.length) : g.add u = g := by
  by_cases hm : g.mem u = true
  · simp [Graph.add, hm]
  · simp [Graph.add, hm] at h

theorem graphMem_of_exists {g : Graph} {t : Triple}
    (h : ∃ u, u ∈ g ∧ Triple.eqb u t = true) : Graph.mem t g = true := by
  obtain ⟨u, hu, he⟩ := h
  induction g with
  | nil => cases hu
  | cons hd tl ih =>
    rcases List.mem_cons.mp hu with rfl | h'
    · simp [Graph.mem, he]
    · simp [Graph.mem, ih h']

/-- Engine membership is closed under the engine equality. -/
theorem graphMem_of_graphMem_eqb {g : Graph} {u t : Triple}
    (h : Graph.mem u g = true) (he : Triple.eqb u t = true) :
    Graph.mem t g = true := by
  obtain ⟨v, hv, hve⟩ := exists_of_graphMem h
  exact graphMem_of_exists ⟨v, hv, Triple.eqb_trans hve he⟩

/-! ## What membership becomes after each set operation

These three say exactly which triples a graph holds after an append,
an add and a remove, in terms of the engine equality rather than
propositional equality. They are what any proof about a sequence of
updates needs, because `Graph.mem` compares with `Triple.eqb` and a
`List.mem` fact says nothing about it.

Proved 2026-08-23 for the delta-merge correctness bridge. The F\* tree
proves the same three about the same functions, for the same reason. -/

theorem mem_append (t : Triple) (l1 l2 : Graph) :
    Graph.mem t (l1 ++ l2) = (Graph.mem t l1 || Graph.mem t l2) := by
  induction l1 with
  | nil => simp [Graph.mem]
  | cons hd tl ih => simp [Graph.mem, ih, Bool.or_assoc]

theorem mem_graph_add (q : Triple) (g : Graph) (t : Triple) :
    Graph.mem t (g.add q) = (Graph.mem t g || Triple.eqb q t) := by
  unfold Graph.add
  split
  · rename_i h
    by_cases he : Triple.eqb q t = true
    · simp [he, graphMem_of_graphMem_eqb h he]
    · simp [Bool.eq_false_iff.mpr he]
  · simp [mem_append, Graph.mem]

/-- Set-union membership.  The executable representation is a list, but this
    lemma keeps callers from accidentally turning a repeated INSERT into two
    RDF graph members. -/
theorem mem_graph_union (g1 g2 : Graph) (t : Triple) :
    Graph.mem t (Graph.union g1 g2) = (Graph.mem t g1 || Graph.mem t g2) := by
  induction g2 generalizing g1 with
  | nil => simp [Graph.union, Graph.mem]
  | cons hd tl ih =>
      change Graph.mem t (Graph.union (Graph.add hd g1) tl) =
        (Graph.mem t g1 || Graph.mem t (hd :: tl))
      rw [ih, mem_graph_add]
      simp [Graph.mem, Bool.or_assoc]

theorem mem_graph_remove (q : Triple) (g : Graph) (t : Triple) :
    Graph.mem t (Graph.remove q g) = (Graph.mem t g && !Triple.eqb q t) := by
  induction g with
  | nil => simp [Graph.remove, Graph.mem]
  | cons hd tl ih =>
    have hfil : Graph.remove q (hd :: tl)
        = if hd.eqb q then Graph.remove q tl else hd :: Graph.remove q tl := by
      unfold Graph.remove
      cases h : hd.eqb q <;> simp [h]
    rw [hfil]
    cases hq : hd.eqb q with
    | true =>
        rw [if_pos rfl, ih]
        cases ht : hd.eqb t with
        | true =>
            have hqt : Triple.eqb q t = true :=
              Triple.eqb_trans (by rw [Triple.eqb_symm]; exact hq) ht
            simp [Graph.mem, ht, hqt]
        | false => simp [Graph.mem, ht]
    | false =>
        rw [if_neg (by simp), Graph.mem, ih]
        cases hqt : Triple.eqb q t with
        | true =>
            cases ht : hd.eqb t with
            | true =>
                exact absurd
                  (Triple.eqb_trans ht (by rw [Triple.eqb_symm]; exact hqt))
                  (by rw [hq]; simp)
            | false => simp
        | false => simp [Graph.mem]

/-- Membership after a filter, for any predicate that respects the
engine equality. `Graph.remove` is the special case where the
predicate is "not equal to `q`"; the delta merge needs the general
form for its tombstone filter. -/
theorem mem_filter_congr {f : Triple → Bool}
    (hcong : ∀ a b, Triple.eqb a b = true → f a = f b) (t : Triple) (l : Graph) :
    Graph.mem t (l.filter f) = (Graph.mem t l && f t) := by
  induction l with
  | nil => simp [Graph.mem]
  | cons hd tl ih =>
    cases hf : f hd with
    | true =>
        rw [List.filter_cons_of_pos hf, Graph.mem, Graph.mem, ih]
        cases ht : hd.eqb t with
        | true => rw [hcong hd t ht] at hf; simp [hf]
        | false => simp
    | false =>
        rw [List.filter_cons_of_neg (by simp [hf]), ih, Graph.mem]
        cases ht : hd.eqb t with
        | true => rw [hcong hd t ht] at hf; simp [hf]
        | false => simp

/-! ## Which triple positions a reader actually needs

Port of `col_need` from `formal/fstar/RDF.Graph.Executable.fst`. A
columnar reader that already knows a row matches still has to decode
the row's three positions to build a `Triple`. When the caller consumes
only some of them — an OPTIONAL or FILTER that projects one variable —
the rest need not be decoded at all. This record is how a caller says
which ones it needs.

It lives HERE, in the lowest module that both the store readers and the
algebra can see, for the same reason the F\* source puts it in
`RDF.Graph.Executable`: it inverts nobody's dependency edge.

Narrowing `ColNeed` may only change WHICH positions are cheaply
decoded, never which rows match or their order. It carries no flag for
the graph column, because the graph column is always decoded whatever
the query shape. -/
structure ColNeed where
  s : Bool
  p : Bool
  o : Bool
  deriving Repr, DecidableEq, Inhabited

/-- All three positions needed — the "decode everything" baseline, and
the safe default for a caller that has not computed a real `ColNeed`. -/
def colNeedAll : ColNeed := { s := true, p := true, o := true }

/-- No position needed. Only safe when the caller genuinely consumes
none of the pattern's variables. -/
def colNeedNone : ColNeed := { s := false, p := false, o := false }

end L4Factoidal.RDF
