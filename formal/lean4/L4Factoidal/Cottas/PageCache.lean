/-
L4Factoidal.Cottas.PageCache — the LRU page cache, and its bounds.

Port of `formal/fstar/RDF.CottasStore.PageCache.fst` (474 lines) and of
the first three lemmas of
`formal/fstar/RDF.CottasStore.PageCache.Bounds.fst` (463 lines).

An assoc list with monotonically increasing age stamps, keyed by
`(row group, column)`. A `get` bumps the matched entry's age; a `put`
past capacity evicts the smallest age. The list is small — the F\*
banner gives `cap = 64` covering parliament's 26 × 4 surface — so the
linear scan is what the F\* module chose and this keeps it.

## One cache instead of two

The F\* module carries the same LRU bookkeeping twice: `pcache_*` over
`cottas_column` for data pages and `dpcache_*` over `list string` for
dictionary pages. Its own comment gives the reason, and it is about
call sites rather than about the cache: "Kept as a separate small type
instead of parameterizing `page_cache` over a type variable, to avoid
touching every existing `page_cache`-typed call site for an unrelated
change."

Here it is written once, polymorphic in the value type, so
`PageCache ColumnData` and `PageCache (List String)` are the two
instantiations. The bounds lemmas below are then proved once and hold
for both, where the F\* tree would need each proof twice.

## What is proved

The three structural lemmas of `PageCache.Bounds.fst` that concern the
cache itself:

1. `replaceEntry_length` — replacing preserves length.
2. `pcacheGet_length` — a lookup preserves length exactly.
3. `pcachePut_capacity_bound` — a put keeps `length ≤ capacity`.

The third is the one with content, and the F\* module says what it
buys: an edit that drops the eviction step becomes a verification
error rather than a production memory spike.

Its fourth lemma, `walk_candidate_rgs_search_limited_bound`, is about
the LIMIT-pushdown walker in `RDF.CottasStore.fst` (2,825 lines), which
is not ported. That lemma is not here, and `RDF.CottasStore.PageCache.
Bounds` is still counted as not covered for that reason.

## What is NOT here

The cache-wrapped decode wrappers — `pcache_decode_in_row_group` and
its three siblings, plus the dictionary probe — call into
`Parquet.Footer`. The Lean tree has no Parquet reader, so those
wrappers wait on that port. The cache itself does not depend on them.
-/
namespace L4Factoidal.Cottas

/-- `(row-group index, column index)`. -/
abbrev PCacheKey := Nat × Nat

/-- The F\* `key_eq` compares the two components; on `Nat × Nat` that is
    decidable equality, so this is the same predicate written once. -/
def keyEq (k1 k2 : PCacheKey) : Bool := k1 == k2

structure PCacheEntry (α : Type) where
  key   : PCacheKey
  value : α
  age   : Nat

structure PageCache (α : Type) where
  entries  : List (PCacheEntry α)
  clock    : Nat
  capacity : Nat        -- 0 disables the cache: every call is a miss

def pcacheEmpty (α : Type) (capacity : Nat) : PageCache α :=
  { entries := [], clock := 0, capacity := capacity }

def lookupEntry {α : Type} : List (PCacheEntry α) → PCacheKey →
    Option (PCacheEntry α)
  | [], _ => none
  | e :: rest, k => if keyEq e.key k then some e else lookupEntry rest k

def replaceEntry {α : Type} : List (PCacheEntry α) → PCacheKey →
    PCacheEntry α → List (PCacheEntry α)
  | [], _, _ => []
  | e :: rest, k, newE =>
      if keyEq e.key k then newE :: rest else e :: replaceEntry rest k newE

def dropEntry {α : Type} : List (PCacheEntry α) → PCacheKey →
    List (PCacheEntry α)
  | [], _ => []
  | e :: rest, k => if keyEq e.key k then rest else e :: dropEntry rest k

/-- A hit returns the value and a cache whose matched entry's age is
    bumped. A miss returns the cache unchanged. -/
def pcacheGet {α : Type} (cache : PageCache α) (k : PCacheKey) :
    Option α × PageCache α :=
  match lookupEntry cache.entries k with
  | none => (none, cache)
  | some entry =>
      let newClock := cache.clock + 1
      (some entry.value,
       { cache with entries := replaceEntry cache.entries k
                                 { entry with age := newClock },
                    clock := newClock })

def findOldestAux {α : Type} : List (PCacheEntry α) → PCacheKey → Nat →
    Bool → Option PCacheKey
  | [], bestKey, _, found => if found then some bestKey else none
  | e :: rest, bestKey, bestAge, found =>
      if !found then findOldestAux rest e.key e.age true
      else if e.age < bestAge then findOldestAux rest e.key e.age true
      else findOldestAux rest bestKey bestAge true

def findOldest {α : Type} (entries : List (PCacheEntry α)) :
    Option PCacheKey := findOldestAux entries (0, 0) 0 false

/-- The list a put produces before the capacity check: replace in place
    when the key is present, prepend otherwise. -/
def entriesAfter {α : Type} (es : List (PCacheEntry α)) (k : PCacheKey)
    (newE : PCacheEntry α) : List (PCacheEntry α) :=
  match lookupEntry es k with
  | some _ => replaceEntry es k newE
  | none   => newE :: es

/-- Evict the least recently used entry when the list is over
    capacity. Split out so the bound below is a statement about the
    eviction step alone. -/
def capEntries {α : Type} (after : List (PCacheEntry α)) (capacity : Nat) :
    List (PCacheEntry α) :=
  if after.length > capacity then
    match findOldest after with
    | none        => after               -- unreachable for a non-empty list
    | some victim => dropEntry after victim
  else after

def pcachePut {α : Type} (cache : PageCache α) (k : PCacheKey) (v : α)
    (capacity : Nat) : PageCache α :=
  if capacity = 0 then cache
  else
    let newClock := cache.clock + 1
    { entries := capEntries (entriesAfter cache.entries k
                    { key := k, value := v, age := newClock }) capacity,
      clock := newClock, capacity := capacity }

/-! ## Bounds

The three structural lemmas of `PageCache.Bounds.fst` that are about
the cache itself. -/

theorem replaceEntry_length {α : Type} (es : List (PCacheEntry α))
    (k : PCacheKey) (newE : PCacheEntry α) :
    (replaceEntry es k newE).length = es.length := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
      cases h : keyEq e.key k with
      | true => simp [replaceEntry, h]
      | false => simp [replaceEntry, h, List.length_cons, ih]

theorem pcacheGet_length {α : Type} (cache : PageCache α) (k : PCacheKey) :
    (pcacheGet cache k).2.entries.length = cache.entries.length := by
  unfold pcacheGet
  cases lookupEntry cache.entries k with
  | none => rfl
  | some entry => simpa using replaceEntry_length cache.entries k _

/-- `findOldestAux` with `found = true` always answers. -/
theorem findOldestAux_isSome {α : Type} (es : List (PCacheEntry α))
    (bk : PCacheKey) (ba : Nat) : ∃ k, findOldestAux es bk ba true = some k := by
  induction es generalizing bk ba with
  | nil => exact ⟨bk, rfl⟩
  | cons e rest ih =>
      simp only [findOldestAux, Bool.not_true]
      by_cases h : e.age < ba
      · simpa [h] using ih e.key e.age
      · simpa [h] using ih bk ba

theorem findOldest_isSome {α : Type} (e : PCacheEntry α)
    (rest : List (PCacheEntry α)) :
    ∃ k, findOldest (e :: rest) = some k := by
  simpa [findOldest, findOldestAux] using findOldestAux_isSome rest e.key e.age

/-- Whatever `findOldestAux` answers is the key of an entry it saw, or
    the running best it was handed. -/
theorem findOldestAux_mem {α : Type} (es : List (PCacheEntry α))
    (bk : PCacheKey) (ba : Nat) (found : Bool) (k : PCacheKey)
    (h : findOldestAux es bk ba found = some k) :
    (∃ e ∈ es, e.key = k) ∨ (found = true ∧ k = bk) := by
  induction es generalizing bk ba found with
  | nil =>
      cases found with
      | false => simp [findOldestAux] at h
      | true => right; exact ⟨rfl, by simpa [findOldestAux] using h.symm⟩
  | cons e rest ih =>
      cases found with
      | false =>
          simp only [findOldestAux, Bool.not_false, if_true] at h
          rcases ih e.key e.age true h with hm | ⟨_, hk⟩
          · exact Or.inl (by obtain ⟨x, hx, hxk⟩ := hm; exact ⟨x, List.mem_cons_of_mem _ hx, hxk⟩)
          · exact Or.inl ⟨e, List.mem_cons_self, hk.symm⟩
      | true =>
          simp only [findOldestAux, Bool.not_true] at h
          cases hage : decide (e.age < ba) with
          | true =>
            rw [if_pos (of_decide_eq_true hage)] at h
            rcases ih e.key e.age true h with hm | ⟨_, hk⟩
            · exact Or.inl (by obtain ⟨x, hx, hxk⟩ := hm
                               exact ⟨x, List.mem_cons_of_mem _ hx, hxk⟩)
            · exact Or.inl ⟨e, List.mem_cons_self, hk.symm⟩
          | false =>
            rw [if_neg (of_decide_eq_false hage)] at h
            rcases ih bk ba true h with hm | ⟨_, hk⟩
            · exact Or.inl (by obtain ⟨x, hx, hxk⟩ := hm
                               exact ⟨x, List.mem_cons_of_mem _ hx, hxk⟩)
            · exact Or.inr ⟨rfl, hk⟩

theorem findOldest_mem {α : Type} (es : List (PCacheEntry α)) (k : PCacheKey)
    (h : findOldest es = some k) : ∃ e ∈ es, e.key = k := by
  rcases findOldestAux_mem es (0, 0) 0 false k h with hm | ⟨hf, _⟩
  · exact hm
  · exact absurd hf (by simp)

/-- Dropping a key that is present removes exactly one entry. -/
theorem dropEntry_length_of_mem {α : Type} (es : List (PCacheEntry α))
    (k : PCacheKey) (h : ∃ e ∈ es, e.key = k) :
    (dropEntry es k).length + 1 = es.length := by
  induction es with
  | nil => simp at h
  | cons e rest ih =>
      cases hk : keyEq e.key k with
      | true => simp [dropEntry, hk]
      | false =>
        have hrest : ∃ x ∈ rest, x.key = k := by
          obtain ⟨x, hx, hxk⟩ := h
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact absurd hk (by simp [keyEq, hxk])
          · exact ⟨x, hx', hxk⟩
        simp [dropEntry, hk, List.length_cons, ← ih hrest]

theorem entriesAfter_length_le {α : Type} (es : List (PCacheEntry α))
    (k : PCacheKey) (newE : PCacheEntry α) :
    (entriesAfter es k newE).length ≤ es.length + 1 := by
  unfold entriesAfter
  cases lookupEntry es k with
  | none => simp
  | some _ => simp [replaceEntry_length]

/-- The eviction step alone: a list at most one over capacity comes
    back within it. -/
theorem capEntries_le {α : Type} (after : List (PCacheEntry α))
    (capacity : Nat) (h : after.length ≤ capacity + 1) :
    (capEntries after capacity).length ≤ capacity := by
  unfold capEntries
  rcases Nat.lt_or_ge capacity after.length with hbig | hbig
  · rw [if_pos hbig]
    obtain ⟨e, rest, hcons⟩ : ∃ e rest, after = e :: rest := by
      cases hl : after with
      | nil => rw [hl] at hbig; simp at hbig
      | cons e rest => exact ⟨e, rest, rfl⟩
    obtain ⟨victim, hv⟩ : ∃ victim, findOldest after = some victim := by
      rw [hcons]; exact findOldest_isSome e rest
    simp only [hv]
    have hdrop := dropEntry_length_of_mem after victim
                    (findOldest_mem after victim hv)
    omega
  · rw [if_neg (by omega)]; omega

/-- The lemma the F\* module exists for: a put never leaves the cache
    holding more than `capacity` entries. An edit that dropped the
    eviction step would fail here rather than in production. -/
theorem pcachePut_capacity_bound {α : Type} (cache : PageCache α)
    (k : PCacheKey) (v : α) (capacity : Nat)
    (h : cache.entries.length ≤ capacity) :
    (pcachePut cache k v capacity).entries.length ≤ capacity := by
  unfold pcachePut
  rcases Nat.eq_zero_or_pos capacity with hc | hc
  · rw [if_pos hc]; omega
  · rw [if_neg (by omega)]
    refine capEntries_le _ _ ?_
    have := entriesAfter_length_le cache.entries k
      ({ key := k, value := v, age := cache.clock + 1 } : PCacheEntry α)
    omega

/-! ## Build-time checks

### Hit, miss, and the age bump -/

private def c0 : PageCache String := pcacheEmpty String 2
private def c1 : PageCache String := pcachePut c0 (0, 0) "a" 2
private def c2 : PageCache String := pcachePut c1 (0, 1) "b" 2

#guard (pcacheGet c0 (0, 0)).1.isNone
#guard (pcacheGet c1 (0, 0)).1 == some "a"
#guard (pcacheGet c2 (0, 1)).1 == some "b"
#guard c2.entries.length == 2

/-! A hit bumps the clock; a miss does not. -/

#guard (pcacheGet c2 (0, 1)).2.clock == c2.clock + 1
#guard (pcacheGet c2 (9, 9)).2.clock == c2.clock

/-! ### Eviction takes the LEAST RECENTLY USED entry, not the oldest
    inserted

`(0,0)` goes in first, then `(0,1)`. Reading `(0,0)` makes `(0,1)` the
least recently used, so inserting a third entry must evict `(0,1)`. A
cache that evicted by insertion order would drop `(0,0)` and pass a
test that never read anything back. -/

private def c2read : PageCache String := (pcacheGet c2 (0, 0)).2
private def c3 : PageCache String := pcachePut c2read (0, 2) "c" 2

#guard c3.entries.length == 2
#guard (pcacheGet c3 (0, 0)).1 == some "a"
#guard (pcacheGet c3 (0, 2)).1 == some "c"
#guard (pcacheGet c3 (0, 1)).1.isNone

/-! ### Re-putting a present key replaces rather than grows -/

private def c2again : PageCache String := pcachePut c2 (0, 0) "a2" 2

#guard c2again.entries.length == 2
#guard (pcacheGet c2again (0, 0)).1 == some "a2"
#guard (pcacheGet c2again (0, 1)).1 == some "b"

/-! ### Capacity zero disables the cache

Every call is a miss and the cache never grows. -/

private def z0 : PageCache String := pcacheEmpty String 0
private def z1 : PageCache String := pcachePut z0 (0, 0) "a" 0

#guard z1.entries.length == 0
#guard (pcacheGet z1 (0, 0)).1.isNone

/-! ### The bound holds computationally too

Twenty puts into a cache of capacity three. The proof covers one step;
this checks the iterate, which is what a caller does. -/

private def manyPuts : PageCache Nat :=
  (List.range 20).foldl (fun c i => pcachePut c (i / 5, i % 5) i 3)
    (pcacheEmpty Nat 3)

#guard manyPuts.entries.length == 3
#guard manyPuts.entries.length ≤ 3

/-! And the three survivors are the three most recent, which is what
    the eviction policy promises. -/

#guard ((manyPuts.entries.map (·.value)).foldl (fun acc v => acc && v ≥ 17) true)

/-! ### The same cache at a different value type

The F\* tree writes this bookkeeping twice, once per value type. Here
the dictionary-page cache is the same code at `List String`. -/

private def d0 : PageCache (List String) := pcacheEmpty (List String) 2
private def d1 : PageCache (List String) := pcachePut d0 (0, 0) ["x", "y"] 2

#guard (pcacheGet d1 (0, 0)).1 == some ["x", "y"]
#guard d1.entries.length == 1

#print axioms pcachePut_capacity_bound
#print axioms pcacheGet_length

end L4Factoidal.Cottas
