/-
L4Factoidal.Cottas.LazyDict — the populate-on-demand column dictionary.

Port of `formal/fstar/RDF.CottasStore.LazyDict.fst` (83 lines).

## What the F\* module is

Four indexed views over one COTTAS column's distinct tokens, which
populate together on the first lookup of any kind:

| Direction | From | To |
|---|---|---|
| decode | id | typed term |
| decode raw | id | raw column token |
| encode | canonical key | id |
| encode raw | raw token | id |

In F\* the container is `assume new type lazy_dict (a : Type0)` and
every operation is an `assume val` in the `ML` effect, realised in
OCaml as four `Hashtbl.t`, a populate thunk, a loaded flag and a mutex.
The module carries two pure `Tot` helpers, `lookup_id_in_list` and
`lookup_key_in_list`, which exist so callers that must stay `Tot` can
do the lookup against an already-materialised list.

## The port: the same split, but the pure side is the whole semantics

Everything except reading and writing one `IO.Ref` is a pure function
here. `buildLoaded` turns the populate result into the four maps;
`LoadedDict.decodeById` and its three siblings are pure lookups. The
`IO` layer is `ensure`, which reads the ref and populates once. So the
build-time `#guard`s below cover the dictionary's whole meaning, and
what they do not cover is exactly the ref.

`assume val` count: ten in the F\* module, zero here.

## Two differences worth stating

**No universe problem, so no abstract type.** The F\* module pins
`lazy_dict` to `Type0` and keeps it abstract because a concrete record
field propagated universe constraints into `SPARQL11.Store`'s mutually
recursive `eval_*` block and produced "Error 89: incompatible universe
sets" (issue #254, commit f442c13 reverted it). Lean has no such
constraint, so `LazyDict` is an ordinary structure and
`LazyDictRegistry` does not need to exist as a workaround — see that
module's header.

**No mutex.** The OCaml realisation locks around the populate. Here two
concurrent first touches could each run the populate thunk. That
wastes the work; it does not change the answer, because the thunk is a
function of the file's bytes and the ref ends up holding an equal
dictionary either way. If this ever runs under real concurrency, that
is the line to revisit.
-/
import Std.Data.HashMap
import L4Factoidal.RDF.Core

namespace L4Factoidal.Cottas

/-- One entry: id, typed value, raw column token. The populate thunk
    returns the full list in id order. -/
abbrev PopulateResult (α : Type) := List (Nat × α × String)

/-- The four maps, plus the two orders the F\* module exposes through
    `to_typed_list` and `to_raw_list`. -/
structure LoadedDict (α : Type) where
  byId    : Std.HashMap Nat α
  rawById : Std.HashMap Nat String
  idByKey : Std.HashMap String Nat
  idByRaw : Std.HashMap String Nat
  typed   : List α
  raw     : List String

/-- Build all four views in one pass.

    A column's tokens are distinct by construction, so no key should
    repeat. If one does, the LAST entry wins in every map — plain
    `insert` semantics, pinned by a `#guard` below rather than left to
    the reader to guess. -/
def buildLoaded {α : Type} (keyOf : α → String) (entries : PopulateResult α) :
    LoadedDict α :=
  entries.foldl (fun acc (i, v, rawTok) =>
      { byId    := acc.byId.insert i v
      , rawById := acc.rawById.insert i rawTok
      , idByKey := acc.idByKey.insert (keyOf v) i
      , idByRaw := acc.idByRaw.insert rawTok i
      , typed   := acc.typed
      , raw     := acc.raw })
    { byId := ∅, rawById := ∅, idByKey := ∅, idByRaw := ∅
    , typed := entries.map (fun e => e.2.1)
    , raw   := entries.map (fun e => e.2.2) }

def LoadedDict.decodeById {α : Type} (d : LoadedDict α) (i : Nat) : Option α :=
  d.byId[i]?

def LoadedDict.decodeRawById {α : Type} (d : LoadedDict α) (i : Nat) : Option String :=
  d.rawById[i]?

def LoadedDict.encodeByKey {α : Type} (d : LoadedDict α) (k : String) : Option Nat :=
  d.idByKey[k]?

def LoadedDict.encodeByRawToken {α : Type} (d : LoadedDict α) (t : String) : Option Nat :=
  d.idByRaw[t]?

def LoadedDict.size {α : Type} (d : LoadedDict α) : Nat := d.typed.length

/-! ## The lazy container -/

structure LazyDict (α : Type) where
  populate : IO (PopulateResult α)
  keyOf    : α → String
  state    : IO.Ref (Option (LoadedDict α))

def mkLazyDict {α : Type} (populate : IO (PopulateResult α))
    (keyOf : α → String) : IO (LazyDict α) := do
  return { populate := populate, keyOf := keyOf, state := ← IO.mkRef none }

/-- Populate once, then reuse. The only stateful function in the
    module. -/
def LazyDict.ensure {α : Type} (d : LazyDict α) : IO (LoadedDict α) := do
  match ← d.state.get with
  | some loaded => return loaded
  | none =>
      let loaded := buildLoaded d.keyOf (← d.populate)
      d.state.set (some loaded)
      return loaded

def LazyDict.decodeById {α : Type} (d : LazyDict α) (i : Nat) : IO (Option α) :=
  return (← d.ensure).decodeById i

def LazyDict.decodeRawById {α : Type} (d : LazyDict α) (i : Nat) : IO (Option String) :=
  return (← d.ensure).decodeRawById i

def LazyDict.encodeByKey {α : Type} (d : LazyDict α) (k : String) : IO (Option Nat) :=
  return (← d.ensure).encodeByKey k

def LazyDict.encodeByRawToken {α : Type} (d : LazyDict α) (t : String) :
    IO (Option Nat) :=
  return (← d.ensure).encodeByRawToken t

/-- Whether the populate has run. This must NOT populate: it is the
    cheap check callers use to decide whether to populate at all. -/
def LazyDict.isPopulated {α : Type} (d : LazyDict α) : IO Bool :=
  return (← d.state.get).isSome

/-- The entry count, POPULATING if it has not happened yet. Contrast
    `LazyTermCache.size`, which answers `0` on an unpopulated cache
    because its F\* comment says so. Two functions with the same name
    and different triggering behaviour is a trap, so both modules say
    which one they are. -/
def LazyDict.size {α : Type} (d : LazyDict α) : IO Nat :=
  return (← d.ensure).size

def LazyDict.toTypedList {α : Type} (d : LazyDict α) : IO (List α) :=
  return (← d.ensure).typed

def LazyDict.toRawList {α : Type} (d : LazyDict α) : IO (List String) :=
  return (← d.ensure).raw

/-! ## The pure list helpers

Ports of the F\* module's `lookup_id_in_list` and
`lookup_key_in_list`, which exist there so a `Tot` caller can look up
against an already-materialised list rather than entering the `ML`
effect. Nothing in Lean forces that split, but the functions are part
of the module's surface, so they are here. -/

def lookupIdInList {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (i', v) :: rest, i => if i == i' then some v else lookupIdInList rest i

def lookupKeyInList {α : Type} : List (String × α) → String → Option α
  | [], _ => none
  | (k', v) :: rest, k => if k == k' then some v else lookupKeyInList rest k

/-- A hit names a pair that is really in the list. The F\* originals
    carry no such lemma; it is cheap here and it is what a caller
    threading a materialised list actually relies on. -/
theorem lookupIdInList_mem {α : Type} (entries : List (Nat × α)) (i : Nat) (v : α)
    (h : lookupIdInList entries i = some v) : (i, v) ∈ entries := by
  induction entries with
  | nil => simp [lookupIdInList] at h
  | cons e rest ih =>
      obtain ⟨i', v'⟩ := e
      cases hi : (i == i') with
      | false =>
          simp only [lookupIdInList, hi, Bool.false_eq_true, if_false] at h
          exact List.mem_cons_of_mem _ (ih h)
      | true =>
          have hii : i = i' := by simpa using hi
          subst hii
          simp only [lookupIdInList, hi, if_true, Option.some.injEq] at h
          subst h
          exact List.mem_cons_self

/-! ## Build-time checks

Everything except the `IO.Ref` is pure, so everything except the ref is
checked here. What is NOT checked: that `ensure` populates once and
reuses, and that `isPopulated` does not populate. Those need `IO`, and
`#guard` cannot run `IO`. -/

private def fixture : PopulateResult String :=
  [(0, "Alice", "\"Alice\""), (1, "Bob", "\"Bob\""), (2, "Carol", "\"Carol\"")]

private def lower (s : String) : String := s.toLower

private def L : LoadedDict String := buildLoaded lower fixture

/-! ### All four directions -/

#guard L.decodeById 1 == some "Bob"
#guard L.decodeRawById 1 == some "\"Bob\""
#guard L.encodeByKey "bob" == some 1
#guard L.encodeByRawToken "\"Bob\"" == some 1

/-! ### A miss in each direction is `none`, and the four directions do
    not leak into each other: a RAW token is not a key, and a key is
    not a raw token. -/

#guard (L.decodeById 3).isNone
#guard (L.decodeRawById 3).isNone
#guard (L.encodeByKey "dave").isNone
#guard (L.encodeByRawToken "\"Dave\"").isNone
#guard (L.encodeByKey "\"Bob\"").isNone
#guard (L.encodeByRawToken "bob").isNone

/-! ### The canonical key is what `keyOf` says, not the typed value -/

#guard (L.encodeByKey "Bob").isNone
#guard L.encodeByKey (lower "Bob") == some 1

/-! ### Order and size -/

#guard L.typed == ["Alice", "Bob", "Carol"]
#guard L.raw == ["\"Alice\"", "\"Bob\"", "\"Carol\""]
#guard L.size == 3
#guard (buildLoaded lower ([] : PopulateResult String)).size == 0
#guard ((buildLoaded lower ([] : PopulateResult String)).decodeById 0).isNone

/-! ### A repeated key: the LAST entry wins

A column's tokens are distinct, so this should not arise. It is pinned
so the behaviour is stated rather than discovered. -/

private def dup : LoadedDict String :=
  buildLoaded lower [(0, "Bob", "\"Bob\""), (7, "BOB", "\"BOB\"")]

#guard dup.encodeByKey "bob" == some 7
#guard dup.decodeById 0 == some "Bob"
#guard dup.decodeById 7 == some "BOB"
#guard dup.size == 2

/-! ### The pure list helpers -/

#guard lookupIdInList [(0, "a"), (1, "b")] 1 == some "b"
#guard (lookupIdInList [(0, "a")] 5).isNone
#guard lookupKeyInList [("x", 1), ("y", 2)] "y" == some 2
#guard (lookupKeyInList ([] : List (String × Nat)) "y").isNone

/-! Both helpers stop at the FIRST match, where `buildLoaded` keeps the
    last. The two are different lookups and the guards say so. -/

#guard lookupIdInList [(0, "first"), (0, "second")] 0 == some "first"

#print axioms lookupIdInList_mem

end L4Factoidal.Cottas
