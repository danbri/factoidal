/-
Harness.RdfsSemiNaive — `l4rdfs-semi`: does the delta closure agree
with the naive one?

Not part of the verified library: it reads no files but prints scores.

    lake exe l4rdfs-semi [maxChainLength]

## ⚠️ Speed is NOT measured here, and that is a gap

`RDFS.SemiNaive` exists for speed, so this harness was written to
measure speed as well as agreement. It does not. Three versions of the
timing were tried and every one reported 0 ms for both closures while
the process spent 90 seconds of CPU on a run whose largest input is a
100-triple graph:

1. `timed (fun _ => closureFix g)` — but `measure` then called
   `closureFix g` AGAIN for the agreement check, so the closure was
   computed twice and the timed call may have been the cheap one.
2. Each closure computed exactly once, with `.length` to force it —
   still 0 ms.
3. `clockAfter`, which reads the clock through an `if` on the value so
   the pure computation cannot be deferred past the timestamp — still
   0 ms.

`clockAfter` is a working technique: a standalone binary using it
reports 5723 ms for a 20-million-step fold, so the clock and the
forcing are both fine. What has not been established is WHERE the 90
seconds goes. `isNaiveFixpoint` and `sameGraph` are both plausible —
each is superlinear in the closure size, and the closures are 5000
triples — but that is a hypothesis, not a measurement.

So the harness reports AGREEMENT only. A speed column that always reads
0 is worse than no column: it reads as "instant" when the truth is
"not measured". Tracked in
https://github.com/danbri/factoidal/issues/554.

The agreement result stands on its own and is what makes the port
usable: `closureSemiNaiveChecked` returns the naive answer whenever the
delta loop is not a fixed point, so a hole in the delta reasoning costs
a slow run, never a wrong one.
-/
import L4Factoidal.RDFS.SemiNaive
import L4Factoidal.Syntax.NTriples

open L4Factoidal.RDF L4Factoidal.RDFS

namespace Harness.RdfsSemiNaive

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

def iri (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩

/-- `a rdf:type C1`, `C1 ⊑ C2`, …, `C(n-1) ⊑ Cn`. The closure holds
    n `rdf:type` triples and n(n-1)/2 transitive `rdfs:subClassOf`
    triples, so the naive loop's re-derivation cost grows fast. -/
def chainOf (n : Nat) : Graph :=
  ⟨.iri (iri "a"), rdfType, .iri (iri "C1")⟩ ::
  (List.range (n - 1)).map (fun k =>
    (⟨.iri (iri s!"C{k+1}"), rdfsSubClassOf, .iri (iri s!"C{k+2}")⟩ : Triple))

/-- A property hierarchy with a domain and a range, so rows rdfs7,
    rdfs2, rdfs3 and rdfs5 fire as well as rdfs9 and rdfs11. -/
def schemaOf (n : Nat) : Graph :=
  (List.range (n - 1)).map (fun k =>
    (⟨.iri (iri s!"p{k+1}"), rdfsSubPropertyOf, .iri (iri s!"p{k+2}")⟩ : Triple)) ++
  [ ⟨.iri (iri s!"p{n}"), rdfsDomain, .iri (iri "D")⟩,
    ⟨.iri (iri s!"p{n}"), rdfsRange, .iri (iri "R")⟩,
    ⟨.iri (iri "x"), iri "p1", .iri (iri "y")⟩,
    ⟨.iri (iri "D"), rdfsSubClassOf, .iri (iri "DSuper")⟩ ]

/-- Set equality of two graphs. The obvious `a.all (· ∈ b) && b.all (· ∈ a)`
    is O(n²) and, at 5000 triples, costs minutes — more than the closures
    it is checking, which is how the first version of this harness came
    to time out before it measured anything. This sorts both sides'
    canonical N-Triples renderings instead, which is O(n log n). -/
def sameGraph (a b : Graph) : Bool :=
  let key (g : Graph) : List String :=
    (g.map L4Factoidal.Syntax.Triple.toCanonicalNTriples).eraseDups.mergeSort
      (fun x y => decide (x ≤ y))
  key a == key b

/-! ## Measuring -/

structure Row where
  label   : String
  size    : Nat
  outSize : Nat
  agree   : Bool
  ownFix  : Bool   -- the delta loop reached the fixpoint without the fallback


def measure (label : String) (g : Graph) : IO Row := do
  let naive := closureFix g
  let fast := semiNaive g
  let ownFix := isNaiveFixpoint fast
  let checked := if ownFix then fast else naive
  return { label := label, size := g.length, outSize := naive.length,
           agree := sameGraph checked naive, ownFix := ownFix }

def render (r : Row) : String :=
  s!"  {r.label} in={r.size} out={r.outSize} agree={r.agree} " ++
  s!"delta-reached-fixpoint={r.ownFix}"

def main (args : List String) : IO UInt32 := do
  let maxN := (args.head?.bind String.toNat?).getD 100
  let sizes := [20, 50, 100, maxN].filter (· ≤ maxN) |>.eraseDups
  let mut rows : List Row := []
  IO.println "--- subclass chain (issue #340 shape) ---"
  for n in sizes do
    let r ← measure s!"chain{n}" (chainOf n)
    IO.println (render r)
    rows := r :: rows
  IO.println ""
  IO.println "--- property hierarchy with domain and range ---"
  for n in sizes do
    let r ← measure s!"schema{n}" (schemaOf n)
    IO.println (render r)
    rows := r :: rows
  let agree := rows.countP (·.agree)
  let own := rows.countP (·.ownFix)
  let total := rows.length
  IO.println ""
  IO.println s!"delta vs naive closure: {agree} agree, {total - agree} differ (out of {total})"
  IO.println s!"delta loop reached the fixpoint without the fallback: {own} of {total}"
  IO.println "A case where the fallback fired still AGREES -- it returns the naive answer."
  IO.println "The second line is what says the delta loop did the work."
  IO.println "Speed is NOT measured here. See the module header and issue #554."
  return (if agree == total then 0 else 1)

end Harness.RdfsSemiNaive

def main (args : List String) : IO UInt32 := Harness.RdfsSemiNaive.main args
