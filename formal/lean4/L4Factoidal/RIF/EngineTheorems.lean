/-
L4Factoidal.RIF.EngineTheorems — extensivity and licensing for the RIF
forward-chaining fixpoint.

Port of `formal/fstar/RIF.Core.Refinement.fst` (364 lines): the same two
properties the RDFS closure already has, stated for `RIF.closure`.

1. **EXTENSIVITY** — the fixpoint never drops an input fact.
2. **LICENSING** — every fact one round ADDS is the head-instantiation
   of SOME rule of the program under SOME substitution the body matched.

## One difference from the F* engine, and it is a real one

The F\* `one_round_aux` fires the program's rules IN SEQUENCE against
the graph it is building, so a later rule sees the earlier rules' new
triples WITHIN THE SAME ROUND. `RIF.Core.Eval`'s own comment flags that
order-dependence, and `RIF.Core.Refinement.fst` needs the "two-graph
src/seed" idiom because of it: its licensing statement has to quantify
over a snapshot EXTENDING the round's input rather than over the input
itself.

`RIF.step` here folds over the rules accumulating into `acc`, but every
rule matches against the round's ORIGINAL `facts`:

```lean
def step (rules : List Rule) (facts : Facts) : Facts × Bool :=
  rules.foldl (fun (acc, blk) r =>
    …  let (ss, b) := matchFormula facts [] body  …) ([], false)
```

So a round is a function of its input alone, rule order does not change
which facts it derives, and licensing is a SINGLE-graph statement. That
is a stronger property, not a weaker one: `Licensed rules facts f` below
names the round's own input, so a reader does not have to reason about
which rules happened to fire first.

The `#guard` block pins the difference rather than asserting it: a
two-rule program where the second rule's body is derivable only by the
first derives NOTHING in one round here, and needs a second round.

## What licensing does NOT say

It does not say the derived fact is TRUE under any semantics. It says
the engine only emits head-instantiations of its own rules — a
provenance property. Truth needs a model theory the RIF port does not
carry, and calling this soundness would be reading provenance as truth.
-/
import L4Factoidal.RIF.Engine

namespace L4Factoidal.RIF

/-! ## A fold that only appends

Both of `step`'s folds accumulate by `acc ++ …`, so membership in the
result is membership in the seed or in one item's contribution. Proving
that once keeps the two licensing inductions short. -/

theorem mem_foldl_append {α β : Type} (g : α → List β) (bstep : α → Bool) :
    ∀ (l : List α) (init : List β) (b0 : Bool) (x : β),
      x ∈ (l.foldl (fun (p : List β × Bool) a => (p.1 ++ g a, p.2 || bstep a))
             (init, b0)).1 →
      x ∈ init ∨ ∃ a ∈ l, x ∈ g a := by
  intro l
  induction l with
  | nil => intro init b0 x hx; exact Or.inl (by simpa using hx)
  | cons a rest ih =>
      intro init b0 x hx
      simp only [List.foldl_cons] at hx
      rcases ih (init ++ g a) (b0 || bstep a) x hx with h | ⟨a', ha', hx'⟩
      · rcases List.mem_append.mp h with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ⟨a, by simp, h2⟩
      · exact Or.inr ⟨a', by simp [ha'], hx'⟩

/-! ## Licensing -/

/-- What one round is allowed to emit: the head of a rule of the
program, instantiated by a substitution the body matched against the
ROUND'S INPUT. A body-less rule is the degenerate case, instantiated
under the empty substitution. -/
def Licensed (rules : List Rule) (facts : Facts) (f : GAtom) : Prop :=
  ∃ r ∈ rules,
    (r.body = none ∧ (instantiate [] r.head).1 = some f)
    ∨ (∃ body, r.body = some body ∧
         ∃ s ∈ (matchFormula facts [] body).1, (instantiate s r.head).1 = some f)

/-- The inner fold over one rule's substitutions emits only
instantiations of that rule's head. -/
theorem mem_derived {r : Rule} {facts : Facts} {body : Formula} {f : GAtom}
    (h : f ∈ (((matchFormula facts [] body).1).foldl
            (fun (a2 : Facts × Bool) s =>
              match instantiate s r.head with
              | (some g, b3) => (a2.1 ++ [g], a2.2 || b3)
              | (none, b3)   => (a2.1, a2.2 || b3)) ([], false)).1) :
    ∃ s ∈ (matchFormula facts [] body).1, (instantiate s r.head).1 = some f := by
  have hg : ∀ (s : Subst),
      (match instantiate s r.head with
       | (some g, b3) => ([f] ++ [g], b3)
       | (none, b3)   => ([f], b3)) = ([f], false) → True := fun _ _ => trivial
  -- Rewrite the fold into the append shape `mem_foldl_append` covers.
  have hshape : (((matchFormula facts [] body).1).foldl
            (fun (a2 : Facts × Bool) s =>
              match instantiate s r.head with
              | (some g, b3) => (a2.1 ++ [g], a2.2 || b3)
              | (none, b3)   => (a2.1, a2.2 || b3)) ([], false))
          = (((matchFormula facts [] body).1).foldl
              (fun (p : Facts × Bool) s =>
                (p.1 ++ (match (instantiate s r.head).1 with
                         | some g => [g] | none => []),
                 p.2 || (instantiate s r.head).2)) ([], false)) := by
    congr 1
    funext p s
    rcases hi : instantiate s r.head with ⟨o, b3⟩
    cases o <;> simp [hi]
  rw [hshape] at h
  rcases mem_foldl_append
      (fun s => match (instantiate s r.head).1 with | some g => [g] | none => [])
      (fun s => (instantiate s r.head).2) _ [] false f h with h0 | ⟨s, hs, hxs⟩
  · simp at h0
  · refine ⟨s, hs, ?_⟩
    rcases hi : (instantiate s r.head).1 with _ | g
    · rw [hi] at hxs; simp at hxs
    · rw [hi] at hxs
      simp only [List.mem_singleton] at hxs
      subst hxs
      first | exact hi | rfl

/-- The contribution of one rule to a round, as a list. Naming it makes
the fold's shape visible and keeps the rewrite below one `congr`. -/
def ruleContrib (facts : Facts) (r : Rule) : Facts :=
  match r.body with
  | none => match (instantiate [] r.head).1 with
            | some g => [g]
            | none   => []
  | some body =>
      (((matchFormula facts [] body).1).foldl
        (fun (a2 : Facts × Bool) s =>
          match instantiate s r.head with
          | (some g, b3) => (a2.1 ++ [g], a2.2 || b3)
          | (none, b3)   => (a2.1, a2.2 || b3)) ([], false)).1

def ruleBlocked (facts : Facts) (r : Rule) : Bool :=
  match r.body with
  | none => (instantiate [] r.head).2
  | some body =>
      (matchFormula facts [] body).2 ||
        (((matchFormula facts [] body).1).foldl
          (fun (a2 : Facts × Bool) s =>
            match instantiate s r.head with
            | (some g, b3) => (a2.1 ++ [g], a2.2 || b3)
            | (none, b3)   => (a2.1, a2.2 || b3)) ([], false)).2

theorem step_eq_fold (rules : List Rule) (facts : Facts) :
    step rules facts
      = rules.foldl (fun (p : Facts × Bool) r =>
          (p.1 ++ ruleContrib facts r, p.2 || ruleBlocked facts r)) ([], false) := by
  simp only [step]
  congr 1
  funext p r
  cases hb : r.body with
  | none =>
      rcases hi : instantiate [] r.head with ⟨o, b⟩
      cases o <;> simp [hb, hi, ruleContrib, ruleBlocked]
  | some body =>
      simp only [hb, ruleContrib, ruleBlocked, Prod.mk.injEq]
      refine ⟨rfl, ?_⟩
      generalize (matchFormula facts [] body).snd = b1
      generalize (List.foldl
          (fun (x : Facts × Bool) s =>
            match instantiate s r.head with
            | (some f, b3) => (x.1 ++ [f], x.2 || b3)
            | (none, b3) => (x.1, x.2 || b3))
          ([], false) (matchFormula facts [] body).1).snd = b2
      cases p.snd <;> cases b1 <;> cases b2 <;> rfl

/-- **Licensing.** Every fact one round emits is licensed by the
program against that round's own input. -/
theorem step_licensed (rules : List Rule) (facts : Facts) (f : GAtom)
    (h : f ∈ (step rules facts).1) : Licensed rules facts f := by
  rw [step_eq_fold] at h
  rcases mem_foldl_append (ruleContrib facts) (ruleBlocked facts) rules [] false f h
    with h0 | ⟨r, hr, hf⟩
  · simp at h0
  · refine ⟨r, hr, ?_⟩
    cases hb : r.body with
    | none =>
        left
        refine ⟨by first | exact hb | rfl, ?_⟩
        simp only [ruleContrib, hb] at hf
        rcases hi : (instantiate [] r.head).1 with _ | g
        · rw [hi] at hf; simp at hf
        · rw [hi] at hf
          simp only [List.mem_singleton] at hf
          subst hf
          first | exact hi | rfl
    | some body =>
        right
        refine ⟨body, by first | exact hb | rfl, ?_⟩
        simp only [ruleContrib, hb] at hf
        exact mem_derived hf

/-! ## Extensivity -/

/-- **Extensivity.** The fixpoint never drops an input fact, at any
round bound. -/
theorem closure_extensive (rules : List Rule) : ∀ (rounds : Nat) (facts : Facts)
    (f : GAtom), f ∈ facts → f ∈ (closure rules facts rounds).1 := by
  intro rounds
  induction rounds with
  | zero => intro facts f hf; simpa [closure] using hf
  | succ n ih =>
      intro facts f hf
      simp only [closure]
      split
      · exact hf
      · exact ih _ f (List.mem_append.mpr (Or.inl hf))

/-! ## Pinned behaviour -/

section Pins

private def ex (s : String) : GTerm := .const ("http://example/" ++ s) iriSpace
private def exT (s : String) : Tm := .const ("http://example/" ++ s) iriSpace

private def factA : GAtom := .member (ex "a") (ex "A")

/-- `A(x) → B(x)` and `B(x) → C(x)`: the second rule's body is
derivable only by the first. -/
private def ruleAB : Rule :=
  { head := .member (.var "x") (exT "B")
  , body := some (.atom (.member (.var "x") (exT "A"))) }

private def ruleBC : Rule :=
  { head := .member (.var "x") (exT "C")
  , body := some (.atom (.member (.var "x") (exT "B"))) }

/-! ONE round derives `B(a)` and nothing else: the second rule matched
against the round's INPUT, which does not hold `B(a)` yet. This is the
pin for the single-graph round semantics — under the F\* engine's
sequential firing the same round would also derive `C(a)`. -/
#guard (step [ruleAB, ruleBC] [factA]).1 == [GAtom.member (ex "a") (ex "B")]

/-! Rule ORDER does not change that. Under sequential firing it would:
running `ruleBC` first and `ruleAB` second gives the same answer here
only because the round reads its input. -/
#guard (step [ruleBC, ruleAB] [factA]).1 == [GAtom.member (ex "a") (ex "B")]

/-! `C(a)` arrives on the SECOND round, so the fixpoint still reaches
it — the difference is per-round, not in the limit. -/
#guard (closure [ruleAB, ruleBC] [factA] 8).1.contains
        (GAtom.member (ex "a") (ex "C"))

/-! And one round is genuinely not enough, which is what makes the two
guards above say something. -/
#guard !((closure [ruleAB, ruleBC] [factA] 1).1.contains
          (GAtom.member (ex "a") (ex "C")))

/-! Extensivity, on concrete input: the seed fact survives. -/
#guard (closure [ruleAB, ruleBC] [factA] 8).1.contains factA

/-! Non-vacuity: a round with no applicable rule derives nothing, so
the licensing theorem is not about an engine that emits everything. -/
#guard (step [ruleBC] [factA]).1.isEmpty

end Pins

end L4Factoidal.RIF
