import FormalConjectures.CoxDuffy.OrientedChromatic

/-! Complete disproof under the literal published obstruction convention.
The coloring equivalence works at every color count. -/

namespace CoxDuffyProof
open CoxDuffy

def crossArcGraph : SimpleGraph (Fin 4) where
  Adj u v := crossArcExample u v = true ∨ crossArcExample v u = true
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by decide⟩

instance : DecidableRel crossArcGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (crossArcExample u v = true ∨ crossArcExample v u = true))

theorem crossArcExample_coloring_iff {k : ℕ} (c : Fin 4 → Fin k) :
    IsOrientedColoring crossArcExample c ↔
      c 0 ≠ c 1 ∧ c 2 ≠ c 3 ∧ c 0 ≠ c 3 := by
  constructor
  · intro h
    exact ⟨h.1 0 1 (by decide), h.1 2 3 (by decide), h.1 0 3 (by decide)⟩
  · rintro ⟨h01, h23, h03⟩
    constructor
    · intro u v h
      fin_cases u <;> fin_cases v <;> simp_all [crossArcExample]
    · intro u v x y h h' heq
      fin_cases u <;> fin_cases v <;> fin_cases x <;> fin_cases y <;>
        simp_all [crossArcExample, ne_comm]

def crossArcColoringEquiv (k : ℕ) :
    {c : Fin 4 → Fin k // IsOrientedColoring crossArcExample c} ≃
      crossArcGraph.Coloring (Fin k) where
  toFun c := SimpleGraph.Coloring.mk c.val (by
    intro u v h
    rcases h with h | h
    · exact c.property.1 u v h
    · exact (c.property.1 v u h).symm)
  invFun c := ⟨c, (crossArcExample_coloring_iff _).mpr
    ⟨c.valid (by decide), c.valid (by decide), c.valid (by decide)⟩⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by ext v; rfl

theorem conjecture12 : ¬ ∀ (n : ℕ) (A : Fin n → Fin n → Bool), IsOriented A →
    ((∃ (m : ℕ) (G : SimpleGraph (Fin m)),
      ∀ k : ℕ, 0 < k → orientedCount A k = chromaticCount G k) ↔
        ¬ HasObstructingPair A) := by
  intro h
  apply (h 4 crossArcExample crossArcExample_isOriented).mp
    ⟨4, crossArcGraph, fun k _ => Nat.card_congr (crossArcColoringEquiv k)⟩
  exact crossArcExample_hasObstructingPair

end CoxDuffyProof

#print axioms CoxDuffyProof.conjecture12
