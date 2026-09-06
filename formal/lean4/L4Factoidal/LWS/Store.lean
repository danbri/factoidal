/-
L4Factoidal.LWS.Store — the abstract resource store, its laws, and the
reference in-memory instance.

The Linked Web Storage Protocol 1.0 Core draft
(https://w3c.github.io/lws-protocol/lws10-core/) names the operations —
"An operation is any of the following actions that can be performed on a
served resource: create resource, read resource, update resource, delete
resource" — and leaves their section bodies empty. What a backend must
provide is therefore stated here as a structure of pure functions over an
abstract state, and what it must SATISFY is stated as `Prop` fields beside
it. `L4Factoidal.LWS.Operations.step` is written against the structure, so
any backend that satisfies the laws answers the same responses.

`MemStore` is the reference instance: a list of entries, first match wins,
with `put` replacing any entry at the same path. `memStoreLaws` proves it
satisfies every law. It is the instance the wasm operations run.
-/
import L4Factoidal.LWS.Model

namespace L4Factoidal.LWS

open L4Factoidal.RDF

/-! ## The abstract store -/

/-- The operations a backend provides over its own state type `σ`.

`now` and `tick` carry the clock. `now` is the time a mutation stamps into
`Entry.mtime`; `tick` advances it. Neither reads a real clock: a host that
has one sets the state's clock through `L4Factoidal.LWS.Operations`. -/
structure Store (σ : Type) where
  lookup : σ → String → Option Entry
  put    : σ → Entry → σ
  remove : σ → String → σ
  paths  : σ → List String
  now    : σ → Nat
  tick   : σ → σ

/-- The laws every backend must satisfy for `Operations.step` to answer what
the specification says it answers.

* `lookupPutSame` — a write is readable at the path it was written to.
* `lookupPutOther` — a write is invisible at every other path. Without it a
  PUT could change a sibling resource, and the containment correspondence of
  Solid Protocol §4.2 would not hold.
* `lookupRemoveSame` — a delete is a delete.
* `lookupRemoveOther` — a delete touches nothing else. This is the law the
  auxiliary-resource lifecycle of §4.3 needs: deleting a subject resource
  deletes its auxiliaries and nothing besides.
* `pathsLookup` — `paths` enumerates exactly the paths that resolve, which
  is what a container enumerating its members reads.
* `nowTick` — the clock is strictly increasing, so two writes in one request
  sequence never carry the same `Last-Modified`. -/
structure StoreLaws {σ : Type} (S : Store σ) : Prop where
  lookupPutSame   : ∀ s e, S.lookup (S.put s e) e.path = some e
  lookupPutOther  : ∀ s e p, p ≠ e.path → S.lookup (S.put s e) p = S.lookup s p
  lookupRemoveSame : ∀ s p, S.lookup (S.remove s p) p = none
  lookupRemoveOther : ∀ s p q, q ≠ p → S.lookup (S.remove s p) q = S.lookup s q
  pathsLookup     : ∀ s p, (S.paths s).contains p = (S.lookup s p).isSome
  nowTick         : ∀ s, S.now (S.tick s) = S.now s + 1

/-! ## The reference in-memory instance -/

/-- The reference state: the entries, newest first, and the clock. -/
structure MemState where
  entries : List Entry := []
  clock   : Nat := 0
deriving Inhabited

def memLookup (s : MemState) (p : String) : Option Entry :=
  s.entries.find? (fun e => e.path == p)

def memPut (s : MemState) (e : Entry) : MemState :=
  { s with entries := e :: s.entries.filter (fun x => x.path != e.path) }

def memRemove (s : MemState) (p : String) : MemState :=
  { s with entries := s.entries.filter (fun x => x.path != p) }

def memPaths (s : MemState) : List String :=
  s.entries.map (·.path)

/-- The reference `Store`. -/
def MemStore : Store MemState where
  lookup := memLookup
  put    := memPut
  remove := memRemove
  paths  := memPaths
  now    := (·.clock)
  tick   := fun s => { s with clock := s.clock + 1 }

/-! ## The laws, proved for `MemStore` -/

/-- After filtering out every entry at `q`, no entry at `q` is found. -/
theorem find_filter_self (l : List Entry) (q : String) :
    List.find? (fun e => e.path == q) (l.filter (fun x => x.path != q)) = none := by
  induction l with
  | nil => simp
  | cons a t ih =>
      by_cases hq : a.path = q
      · have h1 : (a.path != q) = false := by simp [hq]
        simp [List.filter_cons, h1, ih]
      · have h1 : (a.path != q) = true := by simp [hq]
        have h2 : (a.path == q) = false := by simp [hq]
        simp [List.filter_cons, h1, List.find?_cons, h2, ih]

/-- Filtering out the entries at `q` does not change what is found at a
different path `p`. -/
theorem find_filter_ne (l : List Entry) (p q : String) (h : p ≠ q) :
    List.find? (fun e => e.path == p) (l.filter (fun x => x.path != q))
      = List.find? (fun e => e.path == p) l := by
  induction l with
  | nil => simp
  | cons a t ih =>
      by_cases hq : a.path = q
      · have h1 : (a.path != q) = false := by simp [hq]
        have hne : a.path ≠ p := by rw [hq]; exact fun hc => h hc.symm
        have h2 : (a.path == p) = false := by simp [hne]
        simp [List.filter_cons, h1, List.find?_cons, h2, ih]
      · have h1 : (a.path != q) = true := by simp [hq]
        by_cases hp2 : a.path = p
        · have h2 : (a.path == p) = true := by simp [hp2]
          simp [List.filter_cons, h1, List.find?_cons, h2]
        · have h2 : (a.path == p) = false := by simp [hp2]
          simp [List.filter_cons, h1, List.find?_cons, h2, ih]

theorem memLookup_memPut_same (s : MemState) (e : Entry) :
    memLookup (memPut s e) e.path = some e := by
  simp [memLookup, memPut]

theorem memLookup_memPut_other (s : MemState) (e : Entry) (p : String)
    (h : p ≠ e.path) : memLookup (memPut s e) p = memLookup s p := by
  have hp : ¬ (e.path = p) := fun hc => h hc.symm
  simp [memLookup, memPut, hp, find_filter_ne _ _ _ h]

theorem memLookup_memRemove_same (s : MemState) (p : String) :
    memLookup (memRemove s p) p = none := by
  simp [memLookup, memRemove]

theorem memLookup_memRemove_other (s : MemState) (p q : String) (h : q ≠ p) :
    memLookup (memRemove s p) q = memLookup s q := by
  simp [memLookup, memRemove, find_filter_ne _ _ _ h]

/-- `memPaths` lists exactly the paths that resolve. -/
theorem memPaths_memLookup (s : MemState) (p : String) :
    (memPaths s).contains p = (memLookup s p).isSome := by
  simp only [memPaths, memLookup]
  induction s.entries with
  | nil => simp
  | cons a t ih =>
      by_cases hp : a.path = p
      · have h2 : (a.path == p) = true := by simp [hp]
        have h3 : (p == a.path) = true := by rw [hp]; simp
        simp only [List.map_cons, List.contains_cons, h3, Bool.true_or,
                   List.find?_cons, h2, Option.isSome_some]
      · have hne : p ≠ a.path := fun hc => hp hc.symm
        have h2 : (a.path == p) = false := by simp [hp]
        have h3 : (p == a.path) = false := by simp [hne]
        simp only [List.map_cons, List.contains_cons, h3, Bool.false_or,
                   List.find?_cons, h2, ih]

theorem memStoreLaws : StoreLaws MemStore where
  lookupPutSame := memLookup_memPut_same
  lookupPutOther := fun s e p h => memLookup_memPut_other s e p h
  lookupRemoveSame := memLookup_memRemove_same
  lookupRemoveOther := fun s p q h => memLookup_memRemove_other s p q h
  pathsLookup := memPaths_memLookup
  nowTick := fun _ => rfl

end L4Factoidal.LWS
