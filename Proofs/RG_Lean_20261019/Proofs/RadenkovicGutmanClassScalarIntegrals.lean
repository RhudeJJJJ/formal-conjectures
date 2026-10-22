/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanTailIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Gebendorfer.RadenkovicGutman.ClassScalarIntegrals
open Set MeasureTheory
noncomputable section
set_option maxHeartbeats 0

def origin (y : ℝ) : ℝ := Real.log (2/5)+Real.log y
def tail (y : ℝ) : ℝ := -(1/2)/y^2

theorem origin_eq (y : ℝ) (hy : 0 < y) : origin y=Real.log (2*y/5) := by
  have he : (2 : ℝ)*y/5=(2/5)*y := by ring
  rw [he,Real.log_mul (by norm_num) hy.ne']
  rfl

theorem origin_integrable (a : ℝ) : IntervalIntegrable origin volume 0 a :=
  (intervalIntegrable_const).add intervalIntegral.intervalIntegrable_log'

theorem origin_integral (a : ℝ) (ha : 0 < a) :
    (∫ y : ℝ in (0 : ℝ)..a, origin y)=a*(Real.log (2*a/5)-1) := by
  have he : (2 : ℝ)*a/5=(2/5)*a := by ring
  rw [he,Real.log_mul (by norm_num) ha.ne']
  unfold origin
  rw [intervalIntegral.integral_add intervalIntegrable_const
    intervalIntegral.intervalIntegrable_log',intervalIntegral.integral_const,
    integral_log_from_zero]
  simp only [sub_zero,smul_eq_mul]
  ring

theorem tail_eq (y : ℝ) : tail y= -1/(2*y^2) := by
  unfold tail
  ring

theorem tail_integrable_integral (Y : ℝ) (hY : 0 < Y) :
    IntegrableOn tail (Ioi Y) ∧ (∫ y : ℝ in Ioi Y, tail y)= -1/(2*Y) := by
  obtain ⟨hi,he⟩ := TailIntegral.inv_square_integrable_integral (1/2) Y (by norm_num) hY
  have ht : tail=(fun y : ℝ => -((1/2 : ℝ)/y^2)) := by
    funext y
    change -(1/2 : ℝ)/y^2 = -((1/2 : ℝ)/y^2)
    ring
  constructor
  · rw [ht]
    exact hi.neg
  · rw [ht,integral_neg,he]
    ring

/-- The origin estimate has its exact improper integral; a constant lower
bound near zero would lose integrability or the quantitative payment. -/
theorem origin_lower (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0))
    (a : ℝ) (ha : 0 < a) (hb : ∀ y ∈ Ioc (0 : ℝ) a, origin y ≤ f y) :
    a*(Real.log (2*a/5)-1) ≤ ∫ y : ℝ in (0 : ℝ)..a, f y := by
  rw [← origin_integral a ha]
  have hfi := TailIntegral.interval_integrable_of_Ioi hf (le_refl (0 : ℝ)) ha.le
  apply intervalIntegral.integral_mono_on_of_le_Ioo ha.le (origin_integrable a) hfi
  intro y hy
  exact hb y ⟨hy.1,hy.2.le⟩

theorem tail_lower (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0))
    (Y : ℝ) (hY : 0 < Y) (hb : ∀ y ∈ Ioi Y, tail y ≤ f y) :
    -1/(2*Y) ≤ ∫ y : ℝ in Ioi Y, f y := by
  obtain ⟨hi,he⟩ := tail_integrable_integral Y hY
  rw [← he]
  apply integral_mono_ae hi (hf.mono_set (Ioi_subset_Ioi hY.le))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact hb y hy

#print axioms origin_eq
#print axioms origin_integrable
#print axioms origin_integral
#print axioms tail_eq
#print axioms tail_integrable_integral
#print axioms origin_lower
#print axioms tail_lower
end
end Gebendorfer.RadenkovicGutman.ClassScalarIntegrals
