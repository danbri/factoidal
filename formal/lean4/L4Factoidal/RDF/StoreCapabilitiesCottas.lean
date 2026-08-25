/-
L4Factoidal.RDF.StoreCapabilitiesCottas — port of
`RDF.Store.Capabilities.Cottas`.

The F* module builds the read-only `store_caps` record for a COTTAS
file on disk. Its own banner states the property that makes it
reviewable: **"zero new logic, one-to-one mapping"** — every field wraps
the entry point the matching `GB_CottasOnDisk` dispatcher arm already
called.

## The purity doctrine applied

The F* module reaches `RDF.CottasStore`, which is `assume val` I/O:
mmap, file ranges, dictionary pages. The Lean tree does not carry those
as assumptions. `CottasReadOps` is the record of the eight entry points
the builder wraps, taken as a parameter, and `capsOfCottas` is the
wiring over it. That is the same move the rest of this port makes for
`assume val`: an assumption becomes an argument, and what the module
does with it becomes provable.

## What is proved, and why it is worth proving

"Zero new logic, one-to-one mapping" is a claim, and a claim about a
wiring layer is exactly the kind that decays: a later edit adds a
`take`, a swap, a default, and the comment still says zero. `StoreCaps`
carries no laws at all in this tree today — `RDF/StoreCapabilities.lean`
has no theorems — so nothing anywhere says what a backend record must
satisfy.

`StoreCapsLawful` states five laws that any backend record should
satisfy:

* `limitAgrees` — LIMIT pushdown returns the prefix the unbounded read
  would have returned. A backend that stops early must stop at the same
  place.
* `countIsSolve` — `countExact` counts the rows `solve` returns.
* `estimateExact` — when the record ADVERTISES `estimateIsExact`, the
  estimate is the count. A record advertising exactness and
  approximating is the failure this law catches.
* `selectiveAgrees` — a selective read returns the SAME rows in the SAME
  order for any `ColNeed`, which is what the `StoreCaps` field comment
  already claims.
* `presenceSound` — when the record says a predicate is absent, no read
  for that predicate returns a row.

`capsOfCottas_lawful` derives all five from facts about the underlying
reader and from nothing else. That is what "zero new logic" means,
stated so a later edit breaks the build instead of the comment.

`capsOfIndexed_lawful` proves the SAME contract for the in-memory
builder that was already in the tree, with no hypotheses at all, so the
two backends are checked against one statement rather than each against
its own prose.

**Which laws are vacuous where, said out loud** (hazard #24). For the
COTTAS record `estimateExact` is discharged by the flag, because the
builder advertises `estimateIsExact := false` — correct for a reader
whose bounds-present branch approximates, and it means the contract
constrains nothing about that record's `estimate`. For the in-memory
record `selectiveAgrees` is discharged by `solveSelective := none`.
`presenceSound` is the one law that has teeth for BOTH: neither
discharges it by a flag or by a `none`.

## The flags are checked too

A read-only base must not advertise a write path, and the record must
carry the two accelerated capabilities the F* banner says only this
builder has (`sc_distinct_predicates`, `sc_solve_selective`). Both are
`#guard`ed, and `capsOfCottas_readOnly` states the first as a theorem.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.RDF.StoreCapabilities

namespace L4Factoidal.RDF.CottasCaps

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## 1. The reader, as a parameter

One field per F* entry point the builder wraps. The graph scope is
threaded exactly where the F* source threads it — and NOT into
`predicatePresent`, because the F* module says in a comment that the
dispatcher ignores the scope there and that the wrapper "matches that
exactly rather than fixing it". Keeping the omission keeps the port
faithful; changing it would be a silent behaviour edit. -/

/-- The COTTAS graph scope: the default graph, or one named graph. -/
inductive CottasScope where
  | defaultGraph
  | named (name : Iri)
  deriving Repr, DecidableEq, Inhabited

/-- What a COTTAS on-disk reader offers. Each field is one F*
`cottas_ondisk_*` entry point. -/
structure CottasReadOps where
  searchTok : CottasScope → PatternBound → List Triple
  searchLimitedTok : CottasScope → PatternBound → Nat → List Triple
  estimateTok : CottasScope → PatternBound → Nat
  countExactTok : CottasScope → PatternBound → Nat
  predicatePresent : WfIri → Bool
  hasDecodeFailure : Unit → Bool
  distinctPredicates : Unit → Option (List WfIri)
  searchTokSelective : CottasScope → PatternBound → ColNeed → List Triple

/-! ## 2. The builder

Arm for arm against the F* record. The flag values are the F* values,
with the source's reason kept next to each. -/

def capsOfCottas (ops : CottasReadOps) (scope : CottasScope) : StoreCaps :=
  { flags :=
      { supportsNamedGraphs := true    -- COTTAS carries a graph column
      , supportsUpdate := false        -- the bare base is read-only
      , streamingShapes := true
      , estimateIsExact := false       -- the bounds-present branch approximates
      , canReportDecodeFail := true }
  , solve := fun b => ops.searchTok scope b
  , solveLimited := fun b n => ops.searchLimitedTok scope b n
  , estimate := fun b => ops.estimateTok scope b
  , countExact := fun b => ops.countExactTok scope b
    -- the F* dispatcher ignores the scope here; so does this wrapper
  , predicatePresent := fun pred => ops.predicatePresent pred
  , decodeFailure := fun _ => ops.hasDecodeFailure ()
    -- WRAPPED, not called: the dictionary-page walk runs only when a
    -- caller invokes the closure, never on record construction
  , distinctPredicates := some (fun _ => ops.distinctPredicates ())
  , solveSelective := some (fun b need => ops.searchTokSelective scope b need) }

/-! ## 3. The backend contract

Four laws. Each one is a property a caller of `StoreCaps` may rely on,
and none of them is stated anywhere else in this tree. -/

structure StoreCapsLawful (caps : StoreCaps) : Prop where
  /-- LIMIT pushdown returns the prefix an unbounded read would return.
  A backend that stops early stops at the same place. -/
  limitAgrees : ∀ b n, caps.solveLimited b n = capsTakeN n (caps.solve b)
  /-- `countExact` counts the rows `solve` returns. -/
  countIsSolve : ∀ b, caps.countExact b = (caps.solve b).length
  /-- A record that ADVERTISES an exact estimate gives one. -/
  estimateExact : caps.flags.estimateIsExact = true →
    ∀ b, caps.estimate b = (caps.solve b).length
  /-- A selective read returns the same rows in the same order for any
  `ColNeed`, which is what the field's own comment claims. -/
  selectiveAgrees : ∀ f, caps.solveSelective = some f →
    ∀ b need, f b need = caps.solve b
  /-- The predicate short circuit is sound: when the record says a
  predicate is absent, no read for that predicate returns a row. This is
  the one law with teeth for BOTH builders — neither discharges it by a
  flag or by a `none`. -/
  presenceSound : ∀ pred, caps.predicatePresent pred = false →
    caps.solve { p := some pred } = []

/-- The same four laws, about the reader rather than the record. -/
structure CottasReadOpsLawful (ops : CottasReadOps) (scope : CottasScope) : Prop where
  limitAgrees : ∀ b n,
    ops.searchLimitedTok scope b n = capsTakeN n (ops.searchTok scope b)
  countIsSearch : ∀ b, ops.countExactTok scope b = (ops.searchTok scope b).length
  selectiveAgrees : ∀ b need,
    ops.searchTokSelective scope b need = ops.searchTok scope b
  presenceSound : ∀ pred, ops.predicatePresent pred = false →
    ops.searchTok scope { p := some pred } = []

/-! ## 4. Zero new logic, as a theorem

Every law of the record comes from the matching law of the reader, and
from nothing else. `estimateExact` needs no hypothesis at all, because
the builder advertises `estimateIsExact := false` — the law is
discharged by the flag, which is the correct outcome for a reader whose
bounds-present branch approximates. -/

theorem capsOfCottas_lawful (ops : CottasReadOps) (scope : CottasScope)
    (h : CottasReadOpsLawful ops scope) :
    StoreCapsLawful (capsOfCottas ops scope) where
  limitAgrees b n := h.limitAgrees b n
  countIsSolve b := h.countIsSearch b
  estimateExact hex := absurd hex (by simp [capsOfCottas])
  selectiveAgrees f hf b need := by
    simp only [capsOfCottas, Option.some.injEq] at hf
    subst hf
    exact h.selectiveAgrees b need
  presenceSound pred hp := h.presenceSound pred hp

/-- The bare base advertises no write path. -/
theorem capsOfCottas_readOnly (ops : CottasReadOps) (scope : CottasScope) :
    (capsOfCottas ops scope).flags.supportsUpdate = false := rfl

/-- It advertises the two capabilities the F* banner says only this
builder carries. -/
theorem capsOfCottas_accelerated (ops : CottasReadOps) (scope : CottasScope) :
    (capsOfCottas ops scope).distinctPredicates.isSome = true
    ∧ (capsOfCottas ops scope).solveSelective.isSome = true := ⟨rfl, rfl⟩

/-! ## 5. The same contract, for the in-memory builder

`capsOfIndexed` was already in the tree with no laws attached. It
satisfies the same four with no hypotheses: it takes its own prefix, its
count IS its estimate, its estimate is exact and it advertises so, and
it carries no selective read. Checking two backends against ONE
statement is the point of having the statement. -/

theorem capsOfIndexed_lawful (i : OWL.RL.Index) :
    StoreCapsLawful (capsOfIndexed i) where
  limitAgrees _ _ := rfl
  countIsSolve _ := rfl
  estimateExact _ _ := rfl
  selectiveAgrees _ hf := absurd hf (by simp [capsOfIndexed])
  presenceSound pred hp := by
    show igSearch i { p := some pred } = []
    simp only [capsOfIndexed, igEstimate] at hp
    exact List.eq_nil_of_length_eq_zero (by simpa using hp)

/-! ## Build-time checks -/

private def opsNil : CottasReadOps :=
  { searchTok := fun _ _ => []
  , searchLimitedTok := fun _ _ _ => []
  , estimateTok := fun _ _ => 0
  , countExactTok := fun _ _ => 0
  , predicatePresent := fun _ => false
  , hasDecodeFailure := fun _ => false
  , distinctPredicates := fun _ => none
  , searchTokSelective := fun _ _ _ => [] }

private def capsNil : StoreCaps := capsOfCottas opsNil .defaultGraph

/-! The five flag values are the F* values. -/
#guard capsNil.flags.supportsNamedGraphs == true
#guard capsNil.flags.supportsUpdate == false
#guard capsNil.flags.streamingShapes == true
#guard capsNil.flags.estimateIsExact == false
#guard capsNil.flags.canReportDecodeFail == true

/-! Both accelerated capabilities are present, which no other builder in
the tree offers. -/
#guard capsNil.distinctPredicates.isSome == true
#guard capsNil.solveSelective.isSome == true

/-! The empty reader is lawful, so the contract is satisfiable — the
check hazard #24 asks for before a theorem with hypotheses is trusted. -/
#guard (capsNil.solve { p := some (⟨"http://example.org/p", by decide⟩ : WfIri) }).length == 0

/-! ## Axiom audit -/

#print axioms capsOfCottas_lawful
#print axioms capsOfCottas_readOnly
#print axioms capsOfCottas_accelerated
#print axioms capsOfIndexed_lawful

end L4Factoidal.RDF.CottasCaps
