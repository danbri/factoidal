/-
L4Factoidal.OWL.TableauTests — concrete clash derivations (build-time
checked, like every `example` here: elaboration failure = build
failure) and the axiom audit for the soundness theorems.
-/
import L4Factoidal.OWL.TableauTheorems

namespace L4Factoidal.OWL

/-- C ⊓ ¬C at one individual is refuted (complement clash reached
    through both conjunction eliminations). -/
example : Refuted .empty [.inst "a" (.conj (.atom "C") (.neg (.atom "C")))] :=
  .clash (.conjE1 (.hyp (.head _))) (.conjE2 (.hyp (.head _)))

/-- owl:Nothing membership is refuted. -/
example : Refuted .empty [.inst "a" .bot] :=
  .botClash (.hyp (.head _))

/-- ≥1 r with ≤0 r is refuted (count clash). -/
example : Refuted .empty [.inst "a" (.atLeast 1 "r"), .inst "a" (.atMost 0 "r")] :=
  .minMaxClash (.hyp (.head _)) (.hyp (.tail _ (.head _)))

/-- Branching: (⊥ ⊔ ⊥) at an individual is refuted on both
    branches. -/
example : Refuted .empty [.inst "a" (.disj .bot .bot)] :=
  .disjSplit (.hyp (.head _))
    (.botClash (.hyp (.head _)))
    (.botClash (.hyp (.head _)))

/-- The ∀-rule feeds a clash: a ∈ ∀r.⊥ with an r-edge to b refutes. -/
example : Refuted .empty [.inst "a" (.all "r" .bot), .rel "r" "a" "b"] :=
  .botClash (.allE (.hyp (.head _)) (.hyp (.tail _ (.head _))))

/-- The ∃-rule feeding a clash: `a ∈ ∃r.⊥` is refuted through a fresh
    witness that must inhabit owl:Nothing. -/
example : Refuted .empty [.inst "a" (.ex "r" .bot)] :=
  .exWitness "x" (.hyp (.head _)) (by decide)
    (.botClash (.hyp (.tail _ (.head _))))

/-- The textbook unsatisfiable concept: `a ∈ (∃r.C) ⊓ (∀r.¬C)`. The
    fresh witness gets `C` from the ∃-half and `¬C` from the ∀-half
    pushed across the new edge — complement clash. -/
example : Refuted .empty
    [.inst "a" (.conj (.ex "r" (.atom "C")) (.all "r" (.neg (.atom "C"))))] :=
  .exWitness "x" (.conjE1 (.hyp (.head _))) (by decide)
    (.clash
      (.hyp (.tail _ (.head _)))
      (.allE (.conjE2 (.hyp (.tail _ (.tail _ (.head _))))) (.hyp (.head _))))

/-- Transitive role: the r-chain a→b→c meets `∀r.¬C` at `a` and `C`
    at `c` — the composed edge carries the value restriction to the
    chain's end. -/
example : Refuted ⟨[], ["r"]⟩
    [.rel "r" "a" "b", .rel "r" "b" "c",
     .inst "a" (.all "r" (.neg (.atom "C"))), .inst "c" (.atom "C")] :=
  .clash
    (.hyp (.tail _ (.tail _ (.tail _ (.head _)))))
    (.allE (.hyp (.tail _ (.tail _ (.head _))))
      (.transE (.hyp (.head _)) (.hyp (.tail _ (.head _))) (.head _)))

/-- Subrole: an r-edge under `r ⊑ s` triggers a value restriction
    stated on `s`. -/
example : Refuted ⟨[("r", "s")], []⟩
    [.rel "r" "a" "b",
     .inst "a" (.all "s" (.neg (.atom "C"))), .inst "b" (.atom "C")] :=
  .clash
    (.hyp (.tail _ (.tail _ (.head _))))
    (.allE (.hyp (.tail _ (.head _)))
      (.subRoleE (.hyp (.head _)) (.head _)))

/-- The SHIQ showpiece: `a ∈ ∃r.(∃r.C) ⊓ ∀r.¬C` with `r` transitive.
    Two fresh witnesses deep, the ∀⁺-push (`allTransE`) carries the
    value restriction across the first edge so it reaches the second
    witness — complement clash there. -/
example : Refuted ⟨[], ["r"]⟩
    [.inst "a" (.conj (.ex "r" (.ex "r" (.atom "C")))
                      (.all "r" (.neg (.atom "C"))))] :=
  .exWitness "x" (.conjE1 (.hyp (.head _))) (by decide)
    (.exWitness "y" (.hyp (.tail _ (.head _))) (by decide)
      (.clash (.hyp (.tail _ (.head _)))
        (.allE
          (.allTransE
            (.conjE2 (.hyp (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
            (.head _)
            (.hyp (.tail _ (.tail _ (.head _)))))
          (.hyp (.head _)))))

-- Axiom audit. Expected base (proof policy in
-- skills/factoidal-lean-basics): at most propext / Classical.choice /
-- Quot.sound. Measured at landing (2026-08-22): derives_sound is
-- axiom-free; the other two use propext + Quot.sound only.
#print axioms derives_sound
#print axioms refuted_sound
#print axioms refuted_not_consistent

end L4Factoidal.OWL
