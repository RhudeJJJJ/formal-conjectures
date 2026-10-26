module

public import FormalConjectures.Paper.KazemiHypercube
public import Proofs.Kazemi.LowerColor
public import Proofs.Kazemi.Parameters
public import Proofs.Kazemi.Coordinates

/-! # Full proof of the original Kazemi Conjecture 6.1

The coordinate equivalence transfers the explicit syndrome coloring and the
active-class lower bound to the exact hypercube and coloring definitions in the
submitted statement. Every n >= 2 is covered, including the Q5 equality case.
-/

@[expose] public section
namespace Kazemi.Hypercube
open SimpleGraph Kazemi.Certificate

/-- The exact original infinite-family statement, with no extra hypotheses. -/
theorem full_conjecture6_1 (n : ℕ) (hn : 2 ≤ n) :
    totalDominatorChromaticNumber (SimpleGraph.hypercube (2^n+1)) = 2^(2^n-n+1)+2 := by
  classical
  let g := gap n
  let G := SimpleGraph.hypercube (2^n+1)
  let e : Fin (2^n+1) ≃ Index n :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_index])
  let E : Vertex (Fin (2^n+1)) ≃ Vertex (Index n) := coordinateEquiv e
  have hAdj : ∀ u v, (cube (Index n)).Adj (E u) (E v) ↔ G.Adj u v :=
    fun u v => cube_adj_coordinateEquiv e u v
  have hupper : HasTotalDominatorColoring G (g+2) := by
    obtain ⟨f, hproper, hsurj, hdom⟩ := code_coloring n hn
    refine ⟨SimpleGraph.Coloring.mk (fun v => f (E v)) ?_, ?_, ?_⟩
    · intro u v h
      exact hproper _ _ ((hAdj u v).2 h)
    · exact hsurj.comp E.surjective
    · intro v
      obtain ⟨i, hi⟩ := hdom (E v)
      exact ⟨i, fun w hw => (hAdj v w).1 (hi (E w) hw)⟩
  have hlower : ∀ k, HasTotalDominatorColoring G k → g+2 ≤ k := by
    intro k hk
    obtain ⟨c, hsurj, hdom⟩ := hk
    let f : Vertex (Index n) → Fin k := fun x => c (E.symm x)
    have hp : ∀ x y, (cube (Index n)).Adj x y → f x ≠ f y := by
      intro x y h
      apply c.valid
      apply (hAdj (E.symm x) (E.symm y)).1
      simpa only [Equiv.apply_symm_apply] using h
    have hs : Function.Surjective f := hsurj.comp E.symm.surjective
    have hd : ∀ x, ∃ i, ∀ w, f w = i → (cube (Index n)).Adj x w := by
      intro x
      obtain ⟨i, hi⟩ := hdom (E.symm x)
      refine ⟨i, fun w hw => ?_⟩
      have h := (hAdj (E.symm x) (E.symm w)).2 (hi (E.symm w) hw)
      simpa only [Equiv.apply_symm_apply] using h
    exact coloring_lower_bound f hp hs hd (gap n) (dimension_ge_five n hn)
      (gap_ge_dimension n hn) (count_identity n) (total_domination_bound n hn)
  change sInf {k : ℕ | HasTotalDominatorColoring G k} = g+2
  apply le_antisymm (Nat.sInf_le hupper)
  have hmem : sInf {k : ℕ | HasTotalDominatorColoring G k} ∈
      {k : ℕ | HasTotalDominatorColoring G k} := Nat.sInf_mem ⟨g+2, hupper⟩
  exact hlower _ hmem

end Kazemi.Hypercube
