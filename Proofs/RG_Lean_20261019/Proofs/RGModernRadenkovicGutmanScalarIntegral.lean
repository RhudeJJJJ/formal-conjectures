module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The convergent scalar logarithmic integral underlying the Coulson identity.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Lemma 2.4.
-/
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Tactic

@[expose] public section

namespace Gebendorfer.RadenkovicGutman.ScalarIntegral

open Real Set Filter MeasureTheory
open scoped Topology

noncomputable def kernel (a y : ℝ) : ℝ := (1 / 2 : ℝ) * log (1 + (a / y) ^ 2)

noncomputable def primitive (a y : ℝ) : ℝ :=
  y / 2 * log (y ^ 2 + a ^ 2) - y * log y + a * arctan (y / a)

theorem kernel_nonneg (a y : ℝ) : 0 ≤ kernel a y := by
  apply mul_nonneg (by norm_num)
  apply Real.log_nonneg
  nlinarith [sq_nonneg (a / y)]

theorem kernel_log_difference (a y : ℝ) (hy : 0 < y) :
    kernel a y = (1 / 2 : ℝ) * log (y ^ 2 + a ^ 2) - log y := by
  have he : 1 + (a / y) ^ 2 = (y ^ 2 + a ^ 2) / y ^ 2 := by field_simp
  unfold kernel
  rw [he, Real.log_div (by positivity) (by positivity), Real.log_pow]
  ring

theorem primitive_derivative (a y : ℝ) (ha : 0 < a) (hy : 0 < y) :
    HasDerivAt (primitive a) (kernel a y) y := by
  have hp : 0 < y ^ 2 + a ^ 2 := by positivity
  have h1 := ((hasDerivAt_id y).div_const 2).mul
    (((hasDerivAt_id y).pow 2).add_const (a ^ 2) |>.log hp.ne')
  have h2 := (hasDerivAt_id y).mul ((hasDerivAt_id y).log hy.ne')
  have h3 := ((hasDerivAt_id y).div_const a).arctan.const_mul a
  dsimp at h1 h2 h3
  convert! (h1.sub h2).add h3 using 1
  rw [kernel_log_difference a y hy]
  field_simp [hy.ne', ha.ne', hp.ne', show a ^ 2 + y ^ 2 ≠ 0 by positivity]
  ring

theorem primitive_continuousAt_zero (a : ℝ) (ha : 0 < a) :
    ContinuousAt (primitive a) 0 := by
  unfold primitive
  apply ContinuousAt.add
  · apply ContinuousAt.sub
    · apply ContinuousAt.mul (by fun_prop)
      apply ContinuousAt.log (by fun_prop)
      positivity
    · exact Real.continuous_mul_log.continuousAt
  · fun_prop

theorem primitive_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (primitive a) atTop (𝓝 (a * (Real.pi / 2))) := by
  have hsmall : Tendsto (fun y : ℝ => y * kernel a y) atTop (𝓝 0) := by
    have hupper : ∀ᶠ y : ℝ in atTop, y * kernel a y ≤ (a ^ 2 / 2) / y := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have hl := Real.log_le_sub_one_of_pos (show 0 < 1 + (a / y) ^ 2 by positivity)
      have hk : kernel a y ≤ a ^ 2 / (2 * y ^ 2) := by
        calc
          kernel a y ≤ (1 / 2 : ℝ) * (a / y) ^ 2 := by unfold kernel; linarith
          _ = a ^ 2 / (2 * y ^ 2) := by ring
      calc
        y * kernel a y ≤ y * (a ^ 2 / (2 * y ^ 2)) :=
          mul_le_mul_of_nonneg_left hk hy.le
        _ = (a ^ 2 / 2) / y := by field_simp
    have hlower : ∀ᶠ y : ℝ in atTop, 0 ≤ y * kernel a y := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
      exact mul_nonneg hy (kernel_nonneg a y)
    exact squeeze_zero' hlower hupper (tendsto_const_nhds.div_atTop tendsto_id)
  have harctan : Tendsto (fun y : ℝ => a * arctan (y / a)) atTop
      (𝓝 (a * (Real.pi / 2))) := by
    exact tendsto_const_nhds.mul
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp
        (tendsto_id.atTop_div_const ha))
  have hsum := hsmall.add harctan
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [kernel_log_difference a y hy]
  unfold primitive
  ring

theorem kernel_integrable (a : ℝ) (ha : 0 ≤ a) : IntegrableOn (kernel a) (Ioi 0) := by
  rcases ha.eq_or_lt with rfl | ha
  · have he : kernel 0 = fun _ : ℝ => 0 := by funext y; simp [kernel]
    rw [he]
    exact integrableOn_zero
  · exact integrableOn_Ioi_deriv_of_nonneg
      (primitive_continuousAt_zero a ha).continuousWithinAt
      (fun y hy => primitive_derivative a y ha hy) (fun y _ => kernel_nonneg a y)
      (primitive_tendsto a ha)

theorem kernel_integral (a : ℝ) (ha : 0 ≤ a) :
    (∫ y : ℝ in Ioi 0, kernel a y) = a * (Real.pi / 2) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [kernel]
  · have h := integral_Ioi_of_hasDerivAt_of_nonneg
      (primitive_continuousAt_zero a ha).continuousWithinAt
      (fun y hy => primitive_derivative a y ha hy) (fun y _ => kernel_nonneg a y)
      (primitive_tendsto a ha)
    simpa [primitive] using h

theorem shifted_log_norm (a t y : ℝ) (hy : 0 < y) :
    Real.log ‖((t : ℂ) + (y : ℂ) * Complex.I) - (a : ℂ)‖ =
      Real.log y + kernel |a - t| y := by
  have hs : ‖((t : ℂ) + (y : ℂ) * Complex.I) - (a : ℂ)‖ ^ 2 =
      y ^ 2 + (a - t) ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hl := congrArg Real.log hs
  rw [Real.log_pow] at hl
  norm_num at hl
  rw [kernel_log_difference _ y hy, sq_abs]
  linarith

theorem shifted_norm_pos (a t y : ℝ) (hy : 0 < y) :
    0 < ‖((t : ℂ) + (y : ℂ) * Complex.I) - (a : ℂ)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have him := congrArg Complex.im hz
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, zero_add, sub_zero, Complex.zero_im] at him
  linarith

theorem scalar_log_ratio (a b t y : ℝ) (hy : 0 < y) :
    Real.log (‖((t : ℂ) + (y : ℂ) * Complex.I) - (a : ℂ)‖ /
      ‖((t : ℂ) + (y : ℂ) * Complex.I) - (b : ℂ)‖) =
      kernel |a - t| y - kernel |b - t| y := by
  rw [Real.log_div (shifted_norm_pos a t y hy).ne' (shifted_norm_pos b t y hy).ne',
    shifted_log_norm a t y hy, shifted_log_norm b t y hy]
  ring

theorem scalar_log_ratio_integrable (a b t : ℝ) :
    IntegrableOn (fun y : ℝ => Real.log
      (‖((t : ℂ) + (y : ℂ) * Complex.I) - (a : ℂ)‖ /
        ‖((t : ℂ) + (y : ℂ) * Complex.I) - (b : ℂ)‖)) (Ioi 0) := by
  apply ((kernel_integrable |a - t| (abs_nonneg _)).sub
    (kernel_integrable |b - t| (abs_nonneg _))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (scalar_log_ratio a b t y hy).symm

/-- The scalar improper integral, including zero shifted eigenvalues. -/
theorem scalar_log_ratio_integral (a b t : ℝ) :
    (∫ y : ℝ in Ioi 0, Real.log
      (‖((t : ℂ) + (y : ℂ) * Complex.I) - (a : ℂ)‖ /
        ‖((t : ℂ) + (y : ℂ) * Complex.I) - (b : ℂ)‖)) =
      (Real.pi / 2) * (|a - t| - |b - t|) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => scalar_log_ratio a b t y hy),
    integral_sub (kernel_integrable |a - t| (abs_nonneg _))
      (kernel_integrable |b - t| (abs_nonneg _)),
    kernel_integral _ (abs_nonneg _), kernel_integral _ (abs_nonneg _)]
  ring

#print axioms kernel_integrable
#print axioms kernel_integral
#print axioms scalar_log_ratio_integrable
#print axioms scalar_log_ratio_integral

end Gebendorfer.RadenkovicGutman.ScalarIntegral
