/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripPrimitive

/-! The original arsinh integral, including integrability at zero.
The pointwise graph comparisons are separate outstanding obligations. -/
namespace Gebendorfer.RadenkovicGutman.LowStripPrimitive
open Real Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem arsinh_upper (x : ℝ) (hx : 0 ≤ x) :
    arsinh x ≤ log 2+(1/2)*log (1+x^2) := by
  have hs : 0 < sqrt (1+x^2) := Real.sqrt_pos.2 (by positivity)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 1+x^2 by positivity)
  have hle : x ≤ sqrt (1+x^2) := by nlinarith
  have hl := Real.log_le_log (show 0 < x+sqrt (1+x^2) by positivity)
    (show x+sqrt (1+x^2) ≤ 2*sqrt (1+x^2) by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs.ne'] at hl
  have he := congrArg Real.log hsq
  rw [Real.log_pow] at he
  unfold Real.arsinh
  linarith

theorem arsinh_reciprocal_integrable (B : ℝ) :
    IntegrableOn (fun s : ℝ => arsinh (2/s)) (Ioc 0 B) := by
  have hk : IntegrableOn (ScalarIntegral.kernel 2) (Ioc 0 B) :=
    (ScalarIntegral.kernel_integrable 2 (by norm_num)).mono Ioc_subset_Ioi_self le_rfl
  have hc : IntegrableOn (fun _ : ℝ => log 2) (Ioc 0 B) :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => log 2) volume 0 B).1
  have hcont : ContinuousOn (fun s : ℝ => arsinh (2/s)) (Ioc 0 B) := by
    intro s hs
    exact ((continuousAt_const.div continuousAt_id hs.1.ne').arsinh).continuousWithinAt
  apply (hk.add hc).mono' (hcont.aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hspos : 0 < s := hs.1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.arsinh_nonneg_iff.mpr (by positivity))]
  have h := arsinh_upper (2/s) (by positivity : (0 : ℝ) ≤ 2/s)
  dsimp [ScalarIntegral.kernel]
  linarith

theorem primitive_continuous : Continuous primitive := by
  apply continuous_iff_continuousAt.mpr
  intro s
  unfold primitive
  apply ContinuousAt.add
  · apply ContinuousAt.sub
    · apply ContinuousAt.mul (by fun_prop)
      apply ContinuousAt.log (by fun_prop)
      positivity
    · exact Real.continuous_mul_log.continuousAt
  · fun_prop

theorem integral_arsinh_reciprocal (B : ℝ) (hB : 0 < B) :
    (∫ s : ℝ in 0..B, arsinh (2/s)) = primitive B := by
  have hi : IntervalIntegrable (fun s : ℝ => arsinh (2/s)) volume 0 B := by
    refine ⟨arsinh_reciprocal_integrable B, ?_⟩
    simp [show Ioc B (0 : ℝ) = ∅ from Ioc_eq_empty_of_le hB.le]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hB.le
    primitive_continuous.continuousOn
    (fun s hs => primitive_derivative s hs.1) hi
  simpa only [primitive_zero, sub_zero] using h

theorem integral_eight_thirds :
    (∫ s : ℝ in 0..(8/3), arsinh (2/s)) = (8/3)*log 2+2*log 3 := by
  rw [integral_arsinh_reciprocal _ (by norm_num), primitive_eight_thirds]

#print axioms arsinh_reciprocal_integrable
#print axioms integral_eight_thirds
end
end Gebendorfer.RadenkovicGutman.LowStripPrimitive
