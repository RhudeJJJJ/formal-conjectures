/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanTailIntegral

namespace Gebendorfer.RadenkovicGutman.QuantitativePositiveTail
open Set MeasureTheory
noncomputable section

def coefficient (K Y : ℝ) : ℝ := K*Y^2/(2*(Y^2+K))

/-- A quantitative payment, retaining the gain lost by a merely nonnegative tail. -/
theorem pointwise (K Y y q : ℝ) (hK : 0 ≤ K) (hY : 0 < Y) (hy : Y ≤ y)
    (hbound : 1+K/y^2 ≤ q^2) : coefficient K Y/y^2 ≤ Real.log q := by
  have hy0 : 0 < y := hY.trans_le hy
  have hy2 : 0 < y^2 := sq_pos_of_pos hy0
  have hY2 : 0 < Y^2 := sq_pos_of_pos hY
  have hu : 0 < 1+K/y^2 := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos hu
  have he : 1-(1+K/y^2)⁻¹ = K/(y^2+K) := by
    field_simp [hy0.ne',show y^2+K ≠ 0 by positivity]
    <;> ring
  rw [he] at hl
  have hq := Real.log_le_log hu hbound
  rw [Real.log_pow] at hq
  norm_num at hq
  have hsq : Y^2 ≤ y^2 := by nlinarith
  have hb : 2*(coefficient K Y/y^2) ≤ K/(y^2+K) := by
    have hid : 2*(coefficient K Y/y^2) = (K*Y^2/(Y^2+K))/y^2 := by
      unfold coefficient
      field_simp [hy0.ne',show Y^2+K ≠ 0 by positivity]
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0 < y^2)
      (by positivity : 0 < y^2+K)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < Y^2+K)).mpr
    nlinarith [mul_nonneg hK (mul_nonneg hK (sub_nonneg.mpr hsq))]
  linarith

theorem integral_lower (f : ℝ → ℝ) (K Y : ℝ) (hK : 0 ≤ K) (hY : 0 < Y)
    (hf : IntegrableOn f (Ioi Y))
    (hb : ∀ y ∈ Ioi Y, coefficient K Y/y^2 ≤ f y) :
    coefficient K Y/Y ≤ ∫ y : ℝ in Ioi Y, f y := by
  have hc : 0 ≤ coefficient K Y := by unfold coefficient; positivity
  have hi := TailIntegral.inv_square_integrable_integral (coefficient K Y) Y hc hY
  have h := integral_mono_ae hi.1 hf (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hb y hy)
  rw [hi.2] at h
  exact h

#print axioms pointwise
#print axioms integral_lower
end
end Gebendorfer.RadenkovicGutman.QuantitativePositiveTail
