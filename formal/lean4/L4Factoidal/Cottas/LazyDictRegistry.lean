/-
L4Factoidal.Cottas.LazyDictRegistry — path-keyed lookup of a store's
four column dictionaries.

Port of `formal/fstar/RDF.CottasStore.LazyDictRegistry.fst` (52 lines).

## Why the F\* module exists, and why that reason does not apply here

Its header says so directly: issue #254 put four `lazy_dict T` fields
on `cottas_ondisk_handle`, and the abstract type's universe parameters
propagated through `SPARQL11.Store`'s mutually recursive `eval_*`
definitions until F\* reported

```
Error 89: incompatible universe sets for eval_pattern_backend
and eval_select_query_backend_bgp
```

(commit f442c13 reverted it). The fix was to keep `lazy_dict` out of
record fields and reach the dictionaries through path-keyed
`assume val`s instead, so the type appears only in return position.

Lean has no such constraint. `LazyDict` is an ordinary structure and
could sit in a handle record directly. So this module is NOT needed as
a universe workaround.

## What it IS needed for

The keying itself. A cottas store on disk is identified by its path,
several parts of the engine open the same store, and each should get
the dictionaries that are already populated rather than populate its
own copy. That is a real requirement and it survives the port. Five
`assume val`s in F\*; zero here.

## The shape of the port

`Registry β` is a plain path-keyed map, and every operation on it is
pure, so the `#guard`s below cover the keying. The process-global ref
and the four typed accessors are the only `IO`.

⚠️ The registry is process-global, exactly as the OCaml `Hashtbl` is.
Two callers naming the same path share dictionaries. That is the point
and also the hazard: a store rewritten on disk under the same path
keeps serving the old dictionaries until `unregister` is called.
-/
import Std.Data.HashMap
import L4Factoidal.Cottas.LazyDict

namespace L4Factoidal.Cottas

/-! ## The pure keying layer -/

abbrev Registry (β : Type) := Std.HashMap String β

def Registry.empty (β : Type) : Registry β := ∅

def Registry.put {β : Type} (r : Registry β) (path : String) (v : β) : Registry β :=
  r.insert path v

def Registry.find {β : Type} (r : Registry β) (path : String) : Option β :=
  r[path]?

def Registry.has {β : Type} (r : Registry β) (path : String) : Bool :=
  r.contains path

def Registry.drop {β : Type} (r : Registry β) (path : String) : Registry β :=
  r.erase path

/-! ## The four dictionaries of one store -/

structure ColumnDicts where
  subjects   : LazyDict L4Factoidal.RDF.Subject
  predicates : LazyDict L4Factoidal.RDF.WfIri
  objects    : LazyDict L4Factoidal.RDF.Term
  graphs     : LazyDict L4Factoidal.RDF.Iri

/-! ## The process-global registry

One ref, keyed by the store's path, matching the OCaml realisation's
`(string, _) Hashtbl.t` indexed by `coh_path`. -/

initialize lazyDictRegistry : IO.Ref (Registry ColumnDicts) ←
  IO.mkRef (Registry.empty ColumnDicts)

/-- Record a store's dictionaries. Called when a handle is opened. -/
def registerLazyDicts (path : String) (d : ColumnDicts) : IO Unit :=
  lazyDictRegistry.modify (fun r => r.put path d)

/-- Forget a store. Call this when the file at `path` is replaced, or
    the next reader gets the previous file's dictionaries. -/
def unregisterLazyDicts (path : String) : IO Unit :=
  lazyDictRegistry.modify (fun r => r.drop path)

/-- Has a handle been opened at this path? The cheap check callers use
    to decide between populating from scratch and reusing. -/
def isRegistered (path : String) : IO Bool :=
  return (← lazyDictRegistry.get).has path

def getColumnDicts (path : String) : IO (Option ColumnDicts) :=
  return (← lazyDictRegistry.get).find path

def getSubjectsLazy (path : String) :
    IO (Option (LazyDict L4Factoidal.RDF.Subject)) :=
  return (← getColumnDicts path).map (·.subjects)

def getPredicatesLazy (path : String) :
    IO (Option (LazyDict L4Factoidal.RDF.WfIri)) :=
  return (← getColumnDicts path).map (·.predicates)

def getObjectsLazy (path : String) :
    IO (Option (LazyDict L4Factoidal.RDF.Term)) :=
  return (← getColumnDicts path).map (·.objects)

def getGraphsLazy (path : String) :
    IO (Option (LazyDict L4Factoidal.RDF.Iri)) :=
  return (← getColumnDicts path).map (·.graphs)

/-! ## Build-time checks

The keying is pure, so it is checked here at `β := Nat`, which stands
in for `ColumnDicts` — nothing in `Registry` looks at the value. What
is NOT checked: the global ref and the four typed accessors, which need
`IO`. -/

private def r0 : Registry Nat := Registry.empty Nat
private def r1 : Registry Nat := (r0.put "/a/x.cottas" 1).put "/a/y.cottas" 2

#guard !r0.has "/a/x.cottas"
#guard (r0.find "/a/x.cottas").isNone
#guard r1.has "/a/x.cottas"
#guard r1.find "/a/x.cottas" == some 1
#guard r1.find "/a/y.cottas" == some 2

/-! A path is matched WHOLE. A prefix of a registered path, and a path
    that has one as a prefix, are both misses — the failure a
    substring match would produce. -/

#guard (r1.find "/a/x").isNone
#guard (r1.find "/a/x.cottas.old").isNone
#guard (r1.find "/A/X.COTTAS").isNone

/-! Re-registering the same path REPLACES, so reopening a store after
    it is rewritten gives the new dictionaries. -/

#guard (r1.put "/a/x.cottas" 9).find "/a/x.cottas" == some 9

/-! Dropping removes one entry and leaves the others. -/

#guard !(r1.drop "/a/x.cottas").has "/a/x.cottas"
#guard (r1.drop "/a/x.cottas").find "/a/y.cottas" == some 2
#guard !(r1.drop "/a/nothing.cottas").has "/a/nothing.cottas"
#guard (r1.drop "/a/nothing.cottas").find "/a/x.cottas" == some 1

end L4Factoidal.Cottas
