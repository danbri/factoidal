/-
L4Factoidal.RDF.StoreCombine — fold several datasets into one.

Port of `formal/fstar/RDF.Store.Combine.fst` (85 lines).

## What the module does

A command line names several data sources: an in-memory graph, plus one
COTTAS file per `--data-cottas` flag. Each becomes its own dataset. The
evaluator wants ONE dataset. Combining them is two operations:

* the DEFAULT graphs federate, in the order given;
* the NAMED graphs regroup BY IRI — two sources that both carry
  `<http://example/g>` produce one graph named `<http://example/g>`
  whose content is the two put together, in source order.

The F\* module says the regrouping fold used to be written in OCaml with
a `Hashtbl` and a `ref`. This is the ordered list-based form of it.

## What is different here, and why

The F\* version regroups `dataset_backend` values, whose named-graph
entries hold a `graph_backend` — a tagged union with a `GB_Union`
constructor. So its fold has to inspect the tag: when a bucket already
holds a `GB_Union`, it APPENDS to that union's member list, and when the
bucket holds a single backend it wraps the two into a fresh two-element
union. Both arms exist to keep unions FLAT.

The Lean seam has no tag. `RDF.StoreCapabilities` replaced the backend
union with `unionCaps : List StoreCaps → StoreCaps`, a record built from
a member list. So the fold here collects the member LIST per IRI and
calls `unionCaps` once, at the end. Flatness is not something the fold
has to maintain; it is what collecting a list before combining gives.

The one behaviour that IS copied verbatim: a bucket holding exactly one
member is returned as that member, with no union wrapper around it, and
a one-element input list is returned unchanged. `unionCaps [c]` is not
`c` — it overwrites the flags, dropping `supportsUpdate` and
`estimateIsExact` — so wrapping a lone store would silently demote it.

## Order

Both directions of order are preserved and are proved below, not
asserted:

* graph names come out in FIRST-ENCOUNTER order across the input list;
* within one name, members come out in input order, so a solve over the
  combined graph concatenates the per-source solves left to right.

Duplicate names WITHIN one input dataset are all collected, matching the
F\* fold, which adds every `ngb_named` entry it walks. `datasetCapsLookupNamed`
returns a first match, so a dataset carrying the same name twice would
otherwise lose its second entry on combination.
-/
import L4Factoidal.RDF.StoreCapabilities

namespace L4Factoidal.RDF

open L4Factoidal.SPARQL (PatternBound)

/-! ## The regrouping fold -/

/-! Every capability record filed under `n` in one dataset's named list,
in list order. The F\* fold walks every entry, so a repeated name inside
one dataset contributes each of its entries. -/
def capsForName (n : Iri) (named : List (Iri × StoreCaps)) : List StoreCaps :=
  (named.filter (fun p => p.1 == n)).map Prod.snd

/-- The member list filed under `n`, or `[]` when the name is absent.
This is `datasetCapsLookupNamed` on a bucket list. -/
def bucketLookup (n : Iri) : List (Iri × List StoreCaps) → List StoreCaps
  | [] => []
  | (m, cs) :: rest => if m == n then cs else bucketLookup n rest

/-- Add one capability record to `n`'s bucket, creating the bucket at the
END of the list when the name is new. Appending there is what keeps
first-encounter order. -/
def extendBucket (n : Iri) (c : StoreCaps) :
    List (Iri × List StoreCaps) → List (Iri × List StoreCaps)
  | [] => [(n, [c])]
  | (m, cs) :: rest =>
      if m == n then (m, cs ++ [c]) :: rest
      else (m, cs) :: extendBucket n c rest

/-- Fold one dataset's named list into the accumulated buckets. -/
def extendBuckets (acc : List (Iri × List StoreCaps)) :
    List (Iri × StoreCaps) → List (Iri × List StoreCaps)
  | [] => acc
  | (n, c) :: rest => extendBuckets (extendBucket n c acc) rest

/-- Every input dataset's named graphs, regrouped by IRI. -/
def buckets (ds : List DatasetCaps) : List (Iri × List StoreCaps) :=
  ds.foldl (fun acc d => extendBuckets acc d.named) []

/-- One bucket becomes one capability record. A lone member is returned
AS ITSELF: `unionCaps [c]` would rewrite its flags. -/
def collapse : List StoreCaps → StoreCaps
  | [c] => c
  | cs  => unionCaps cs

/-- The combined named-graph list. -/
def combineNamed (ds : List DatasetCaps) : List (Iri × StoreCaps) :=
  (buckets ds).map (fun p => (p.1, collapse p.2))

/-! ## The combiner -/

/-- Fold a list of datasets into one.

* empty list — an empty dataset, the `GB_Union []` of the F\* version
  spelled `unionCaps []`;
* one element — returned unchanged, no wrapper;
* more — defaults federated in order, named graphs regrouped by IRI. -/
def combineDatasetCaps (ds : List DatasetCaps) : DatasetCaps :=
  match ds with
  | []  => { default := unionCaps [], named := [] }
  | [d] => d
  | _   => { default := unionCaps (ds.map DatasetCaps.default)
           , named := combineNamed ds }

/-! ## What the combination answers

`namedSolve` is the reader's view: look the name up, solve the bound
against whatever is filed there, and read an absent name as no rows. -/

def namedSolve (n : Iri) (named : List (Iri × StoreCaps)) (b : PatternBound) :
    List Triple :=
  match datasetCapsLookupNamed n named with
  | some c => c.solve b
  | none   => []

/-! ## Proofs -/

/-- `collapse` solves as the concatenation of its members' solves — the
one-member case included, which is the case that is NOT a `unionCaps`. -/
theorem collapse_solve (cs : List StoreCaps) (b : PatternBound) :
    (collapse cs).solve b = cs.flatMap (fun c => c.solve b) := by
  match cs with
  | [] => simp [collapse, unionCaps, unionSolve]
  | [_] => simp [collapse]
  | _ :: _ :: _ => simp [collapse, unionCaps, unionSolve]

/-- Adding one record appends to that name's bucket and leaves every
other name's bucket alone. Both arms of `extendBucket` — extend in place,
and create at the end — give the same equation. -/
theorem bucketLookup_extendBucket (n m : Iri) (c : StoreCaps)
    (acc : List (Iri × List StoreCaps)) :
    bucketLookup n (extendBucket m c acc)
      = if m = n then bucketLookup n acc ++ [c] else bucketLookup n acc := by
  induction acc with
  | nil => by_cases h : m = n <;> simp [extendBucket, bucketLookup, h]
  | cons p rest ih =>
      obtain ⟨k, cs⟩ := p
      by_cases hkm : k = m
      · subst hkm
        by_cases hkn : k = n
        · subst hkn; simp [extendBucket, bucketLookup]
        · simp [extendBucket, bucketLookup, hkn]
      · by_cases hkn : k = n
        · subst hkn
          have hmn : ¬ m = k := fun h => hkm h.symm
          simp [extendBucket, bucketLookup, hkm, hmn]
        · simp [extendBucket, bucketLookup, hkm, hkn, ih]

/-- Folding one dataset's named list appends exactly that dataset's
entries for `n`, in their own order. -/
theorem bucketLookup_extendBuckets (n : Iri) (acc : List (Iri × List StoreCaps))
    (named : List (Iri × StoreCaps)) :
    bucketLookup n (extendBuckets acc named)
      = bucketLookup n acc ++ capsForName n named := by
  induction named generalizing acc with
  | nil => simp [extendBuckets, capsForName]
  | cons p rest ih =>
      obtain ⟨k, c⟩ := p
      by_cases hkn : k = n
      · subst hkn
        simp [extendBuckets, capsForName, ih, bucketLookup_extendBucket,
              List.append_assoc]
      · simp [extendBuckets, capsForName, ih, bucketLookup_extendBucket, hkn]

/-- Across the whole input list: the bucket for `n` is every input
dataset's entries for `n`, concatenated in input order. -/
theorem bucketLookup_buckets (ds : List DatasetCaps) (n : Iri) :
    bucketLookup n (buckets ds) = ds.flatMap (fun d => capsForName n d.named) := by
  have gen : ∀ (l : List DatasetCaps) (acc : List (Iri × List StoreCaps)),
      bucketLookup n (l.foldl (fun a d => extendBuckets a d.named) acc)
        = bucketLookup n acc ++ l.flatMap (fun d => capsForName n d.named) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons d rest ih =>
        intro acc
        simp [List.foldl_cons, ih, bucketLookup_extendBuckets, List.append_assoc]
  simpa [buckets, bucketLookup] using gen ds []

/-- Reading one name out of a collapsed bucket list is the concatenated
solve of that bucket. This needs NO side condition about empty buckets:
an absent name gives `[]` from the lookup, and a bucket that somehow held
no members would collapse to `unionCaps []`, which also solves to `[]`. -/
theorem namedSolve_map_collapse (n : Iri) (bs : List (Iri × List StoreCaps))
    (b : PatternBound) :
    namedSolve n (bs.map (fun p => (p.1, collapse p.2))) b
      = (bucketLookup n bs).flatMap (fun c => c.solve b) := by
  induction bs with
  | nil => simp [namedSolve, datasetCapsLookupNamed, bucketLookup]
  | cons p rest ih =>
      obtain ⟨k, cs⟩ := p
      by_cases hkn : k = n
      · subst hkn
        simp [namedSolve, datasetCapsLookupNamed, bucketLookup, collapse_solve]
      · simpa [namedSolve, datasetCapsLookupNamed, bucketLookup, hkn] using ih

/-- The reader's view of one named graph of the combination: the rows are
every input dataset's rows for that name, concatenated in input order.

This is the statement the fold exists to make true, and it holds for
every name at once — including a name no input carries, where both sides
are empty. -/
theorem combineNamed_solve (ds : List DatasetCaps) (n : Iri) (b : PatternBound) :
    namedSolve n (combineNamed ds) b
      = (ds.flatMap (fun d => capsForName n d.named)).flatMap (fun c => c.solve b) := by
  rw [combineNamed, namedSolve_map_collapse, bucketLookup_buckets]

/-- The default graph of the combination: every input's default, in
order. All three arms of `combineDatasetCaps` agree with it — the empty
list because `unionCaps []` solves to nothing, and the one-element list
because `flatMap` over a singleton is that element's own rows. -/
theorem combineDatasetCaps_default_solve (ds : List DatasetCaps) (b : PatternBound) :
    (combineDatasetCaps ds).default.solve b
      = ds.flatMap (fun d => d.default.solve b) := by
  match ds with
  | [] => simp [combineDatasetCaps, unionCaps, unionSolve]
  | [_] => simp [combineDatasetCaps]
  | _ :: _ :: _ =>
      simp [combineDatasetCaps, unionCaps, unionSolve, List.flatMap_map,
            ]

/-! ## Pinned behaviour -/

section Pins
open L4Factoidal.SPARQL (patternBoundAll)

private def capsOfList (ts : List Triple) : StoreCaps :=
  capsOfIndexed (OWL.RL.Index.ofGraph ts)

private def iriA : WfIri := ⟨"http://example/a", by decide⟩
private def iriC : WfIri := ⟨"http://example/c", by decide⟩
private def iriB : WfIri := ⟨"http://example/b", by decide⟩
private def iriD : WfIri := ⟨"http://example/d", by decide⟩
private def iriE : WfIri := ⟨"http://example/e", by decide⟩
private def iriP : WfIri := ⟨"http://example/p", by decide⟩
private def iriO : WfIri := ⟨"http://example/o", by decide⟩

private def tri (s : WfIri) : Triple := { s := .iri s, p := iriP, o := .iri iriO }

private def dsA : DatasetCaps :=
  { default := capsOfList [tri iriA]
  , named := [("http://example/g", capsOfList [tri iriB])] }

private def dsB : DatasetCaps :=
  { default := capsOfList [tri iriC]
  , named := [ ("http://example/g", capsOfList [tri iriD])
             , ("http://example/h", capsOfList [tri iriE]) ] }

/-! Two sources sharing a name give one graph with both sources' rows,
in source order. -/
#guard
  (namedSolve "http://example/g" (combineDatasetCaps [dsA, dsB]).named patternBoundAll)
    == [tri iriB, tri iriD]

/-! A name only one source carries survives untouched. -/
#guard
  (namedSolve "http://example/h" (combineDatasetCaps [dsA, dsB]).named patternBoundAll)
    == [tri iriE]

/-! First-encounter order, not sorted order and not reverse order. -/
#guard (combineNamed [dsA, dsB]).map Prod.fst == ["http://example/g", "http://example/h"]

/-! Defaults federate in input order. -/
#guard
  ((combineDatasetCaps [dsA, dsB]).default.solve patternBoundAll)
    == [tri iriA, tri iriC]

/-! A single input is returned unchanged, so its flags survive. The
in-memory builder advertises an EXACT estimate; `unionCaps` does not. -/
#guard (combineDatasetCaps [dsA]).default.flags.estimateIsExact
      == dsA.default.flags.estimateIsExact

/-! And a lone member inside a bucket is not wrapped either. -/
#guard (combineDatasetCaps [dsA, dsB]).named.any (fun p =>
        p.1 == "http://example/h" && p.2.flags.estimateIsExact)

/-! The empty combination reads as an empty dataset rather than failing. -/
#guard ((combineDatasetCaps []).default.solve patternBoundAll).isEmpty
      && (combineDatasetCaps []).named.isEmpty

end Pins

end L4Factoidal.RDF
