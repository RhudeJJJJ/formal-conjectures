/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCoulson

namespace Gebendorfer.RadenkovicGutman.FiniteSpectrumRemainders

open Finset
open scoped Classical
noncomputable section

theorem kernel_upper (a y : ℝ) :
    ScalarIntegral.kernel a y ≤ a ^ 2 / (2 * y ^ 2) := by
  have hl := Real.log_le_sub_one_of_pos
    (show 0 < 1 + (a / y) ^ 2 by positivity)
  calc
    ScalarIntegral.kernel a y ≤ (1 / 2 : ℝ) * (a / y) ^ 2 := by
      unfold ScalarIntegral.kernel
      linarith
    _ = a ^ 2 / (2 * y ^ 2) := by ring

theorem scalar_tail_lower (a b t y : ℝ) (hy : 0 < y) :
    -((b - t) ^ 2 / (2 * y ^ 2)) ≤
      Real.log (‖((t : ℂ) + (y : ℂ) * Complex.I) - (a : ℂ)‖ /
        ‖((t : ℂ) + (y : ℂ) * Complex.I) - (b : ℂ)‖) := by
  rw [ScalarIntegral.scalar_log_ratio a b t y hy]
  have hu := kernel_upper |b - t| y
  rw [sq_abs] at hu
  linarith [ScalarIntegral.kernel_nonneg |a - t| y]

theorem scalar_origin_lower (a b t y B : ℝ) (hy : 0 < y)
    (hy1 : y ≤ 1) (hB : |b - t| ≤ B) :
    Real.log y - Real.log (B + 1) ≤
      Real.log (‖((t : ℂ) + (y : ℂ) * Complex.I) - (a : ℂ)‖ /
        ‖((t : ℂ) + (y : ℂ) * Complex.I) - (b : ℂ)‖) := by
  have hn : ‖((t : ℂ) + (y : ℂ) * Complex.I) - (b : ℂ)‖ ≤ B + 1 := by
    have he : ((t : ℂ) + (y : ℂ) * Complex.I) - (b : ℂ) =
        ((t - b : ℝ) : ℂ) + (y : ℂ) * Complex.I := by push_cast; ring
    rw [he]
    calc
      ‖((t - b : ℝ) : ℂ) + (y : ℂ) * Complex.I‖ ≤
          ‖((t - b : ℝ) : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |b - t| + y := by simp [norm_mul, abs_sub_comm, abs_of_pos hy]
      _ ≤ B + 1 := add_le_add hB hy1
  have hl := Real.log_le_log (ScalarIntegral.shifted_norm_pos b t y hy) hn
  rw [ScalarIntegral.shifted_log_norm b t y hy] at hl
  rw [ScalarIntegral.scalar_log_ratio a b t y hy]
  linarith [ScalarIntegral.kernel_nonneg |a - t| y]

variable {V : Type*} [Fintype V]

theorem spectral_tail_lower (a b : V → ℝ) (t y : ℝ) (hy : 0 < y) :
    -(∑ i, (b i - t) ^ 2) / (2 * y ^ 2) ≤ Coulson.logarithm a b t y := by
  rw [Coulson.logarithm_sum a b t y hy]
  calc
    -(∑ i, (b i - t) ^ 2) / (2 * y ^ 2) =
        ∑ i, -((b i - t) ^ 2 / (2 * y ^ 2)) := by
      rw [Finset.sum_neg_distrib, Finset.sum_div]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun i _ => scalar_tail_lower (a i) (b i) t y hy)

theorem spectral_origin_lower (a b : V → ℝ) (t y B : ℝ) (hy : 0 < y)
    (hy1 : y ≤ 1) (hB : ∀ i, |b i - t| ≤ B) :
    (Fintype.card V : ℝ) * (Real.log y - Real.log (B + 1)) ≤
      Coulson.logarithm a b t y := by
  rw [Coulson.logarithm_sum a b t y hy]
  calc
    (Fintype.card V : ℝ) * (Real.log y - Real.log (B + 1)) =
        ∑ _i : V, (Real.log y - Real.log (B + 1)) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => scalar_origin_lower (a i) (b i) t y B hy hy1 (hB i))

#print axioms kernel_upper
#print axioms scalar_tail_lower
#print axioms scalar_origin_lower
#print axioms spectral_tail_lower
#print axioms spectral_origin_lower

end
end Gebendorfer.RadenkovicGutman.FiniteSpectrumRemainders
