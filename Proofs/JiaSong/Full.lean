module

public import Proofs.JiaSong.Spectrum
public import Proofs.JiaSong.Bounds

/-! # Full original negative Jia--Song Conjecture 3.8

The actual graph `twoCliqueJoin 5` violates the published lower bound.
This certifies exactly the original negative endpoint in PR7400. The corrected
all-order minimum and equality statements are separate targets.
Source: Jia--Song (2018), Conjecture3.8, and the linked v2 manuscript's H5 witness.
-/

@[expose] public section
namespace JiaSong
open Certificate

theorem objective_bowtie : objective H = 4 - Real.sqrt 41 / 2 := by
  rw [objective, remoteness_value, second_eigenvalue]
  dsimp [lowerRoot]
  ring

theorem strict_counterexample : objective H < conjecturedBound 5 := by
  convert Certificate.radical_comparison using 1 <;>
    norm_num [objective_bowtie, conjecturedBound]

/-- Full exact original quantified refutation, witnessed by the actual bowtie. -/
theorem full_conjecture3_8 : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj], 4 ≤ n → G.Connected →
      2 ≤ n.choose 2 - G.edgeFinset.card → conjecturedBound n ≤ objective G := by
  intro h
  have hbound := h 5 H (by decide) connected (by rw [edge_count]; decide)
  exact (not_le_of_gt strict_counterexample) hbound

end JiaSong
