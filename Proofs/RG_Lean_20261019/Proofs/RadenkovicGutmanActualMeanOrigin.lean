/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectrumIntegralRemainders
import Proofs.RadenkovicGutmanActualFusionIntegral

namespace Gebendorfer.RadenkovicGutman.ActualMeanOrigin

open Finset Set MeasureTheory
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

attribute [-instance] SimpleGraph.fintypeEdgeSetSup

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem spectrum_nonneg (G : SimpleGraph V) (i : V) :
    0 ≤ laplacianSpectrum G i := by
  exact (SimpleGraph.posSemidef_lapMatrix ℝ G).eigenvalues_nonneg i

theorem spectrum_upper (G : SimpleGraph V) (i : V) :
    laplacianSpectrum G i ≤ (Fintype.card V : ℝ) ^ 2 := by
  have hd := congrArg (fun n : ℕ => (n : ℝ)) G.sum_degrees_eq_twice_card_edges
  push_cast at hd
  calc
    laplacianSpectrum G i ≤ ∑ j, laplacianSpectrum G j :=
      Finset.single_le_sum (fun j _ => spectrum_nonneg G j) (Finset.mem_univ i)
    _ = (2 * G.edgeFinset.card : ℝ) := spectrum_sum G
    _ = ∑ j, (G.degree j : ℝ) := hd.symm
    _ ≤ ∑ _j : V, (Fintype.card V : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact_mod_cast (G.degree_lt_card_verts j).le
    _ = (Fintype.card V : ℝ) ^ 2 := by simp [pow_two]

theorem shifted_spectrum_bound (G : SimpleGraph V) (n : ℕ)
    (hN : Fintype.card V ≤ n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) (i : V) :
    |laplacianSpectrum G i - t| ≤ (n : ℝ) ^ 2 + 2 := by
  have hc : (Fintype.card V : ℝ) ≤ n := by exact_mod_cast hN
  have hs := pow_le_pow_left₀ (show (0 : ℝ) ≤ Fintype.card V by positivity) hc 2
  have hn := spectrum_nonneg G i
  have hu := spectrum_upper G i
  apply abs_le.mpr
  constructor <;> linarith [ht.1,ht.2,sq_nonneg (n : ℝ)]

theorem mixed_origin_lower {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hc : Fintype.card V = Fintype.card W)
    (n : ℕ) (hN : Fintype.card V ≤ n) (t ε : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 2) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (n : ℝ) * ε * (Real.log ε - Real.log ((n : ℝ) ^ 2 + 3) - 1) ≤
      ∫ y : ℝ in (0 : ℝ)..ε, MixedGraphIntegral.logarithm G H t y := by
  let e : V ≃ W := Fintype.equivOfCardEq hc
  let H' : SimpleGraph V := H.comap e
  let f : H' ≃g H := { toEquiv := e, map_rel_iff' := by intro a b; rfl }
  have he : MixedGraphIntegral.logarithm G H t = GraphIntegral.graphLogarithm G H' t := by
    funext y
    unfold MixedGraphIntegral.logarithm GraphIntegral.graphLogarithm
    rw [MixedGraphIntegral.shifted_det_eq f]
  rw [he, GraphIntegral.graphLogarithm_eq G H' t]
  simp_rw [Coulson.matrixLogarithm_eq _ _ (G.isHermitian_lapMatrix ℝ)
    (H'.isHermitian_lapMatrix ℝ) t]
  have hbound (i : V) : |(H'.isHermitian_lapMatrix ℝ).eigenvalues i - t| ≤
      (n : ℝ) ^ 2 + 2 := shifted_spectrum_bound H' n hN t ht i
  have hspec := FiniteSpectrumIntegralRemainders.spectral_origin_integral_lower
    (G.isHermitian_lapMatrix ℝ).eigenvalues (H'.isHermitian_lapMatrix ℝ).eigenvalues
    t ((n : ℝ) ^ 2 + 2) ε hε hε1 hbound
  rw [show ((n : ℝ) ^ 2 + 2) + 1 = (n : ℝ) ^ 2 + 3 by ring] at hspec
  have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have hlogB : 0 ≤ Real.log ((n : ℝ) ^ 2 + 3) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (n : ℝ)])
  have hneg : ε * (Real.log ε - Real.log ((n : ℝ) ^ 2 + 3) - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hε.le (by linarith)
  have hcoef := mul_le_mul_of_nonpos_right
    (show (Fintype.card V : ℝ) ≤ n by exact_mod_cast hN) hneg
  have hcoef' : (n : ℝ) * ε * (Real.log ε - Real.log ((n : ℝ) ^ 2 + 3) - 1) ≤
      (Fintype.card V : ℝ) * ε * (Real.log ε - Real.log ((n : ℝ) ^ 2 + 3) - 1) := by
    simpa only [mul_assoc] using hcoef
  exact hcoef'.trans hspec

/-- The order bound refers to the same actual source/fused Laplace matrices. -/
theorem actual_origin_lower (C : SimpleGraph V) (u : V) (p q n : ℕ)
    (hN : Fintype.card V + p + q + 2 ≤ n) (t ε : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 2) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (n : ℝ) * ε * (Real.log ε - Real.log ((n : ℝ) ^ 2 + 3) - 1) ≤
      ∫ y : ℝ in (0 : ℝ)..ε,
        MixedGraphIntegral.logarithm (CoreQuotient.source C u p q)
          (CoreQuotient.fused C u p q) t y := by
  apply mixed_origin_lower _ _ (ActualFusionIntegral.source_fused_card (V := V) p q)
    n ?_ t ε ht hε hε1
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

#print axioms spectrum_nonneg
#print axioms spectrum_upper
#print axioms shifted_spectrum_bound
#print axioms mixed_origin_lower
#print axioms actual_origin_lower

attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.ActualMeanOrigin
