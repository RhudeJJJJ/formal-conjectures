import Proofs.WOWII364Proof

namespace WOWII364Audit
open WOWII364Proof SimpleGraph Finset

/-- The support predicate is adjacency to a leaf of the original graph. -/
lemma support_spec {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    v ∈ supports G ↔ ∃ w, G.degree w = 1 ∧ G.Adj v w := by simp [supports]

lemma witness_degrees : ∀ v : Fin 4,
    witness.degree v = if v = 0 ∨ v = 3 then 1 else 2 := by decide

lemma damaged_selection : ¬ witness.IsTotalDominating ({1} : Set (Fin 4)) := by
  intro h
  obtain ⟨w, hw, ha⟩ := h 1
  have hw1 : w = 1 := hw
  subst w
  exact ha.ne rfl

/-- The theorem concludes the complete negated universal statement. -/
example : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
      ((supports G).card : ℚ) + (edgesOn G (degreeTwo G) : ℚ) / 2 ≤
        G.totalDominationNumber := conjecture364

#print axioms WOWII364Proof.conjecture364
#print axioms witness_degrees
#print axioms damaged_selection
end WOWII364Audit
