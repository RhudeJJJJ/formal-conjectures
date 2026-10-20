/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanScalarIntegral
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! Calculus for the original small-ordinate integral.  No graph-sign
certificate or complete degree family is asserted by this module. -/
namespace Gebendorfer.RadenkovicGutman.LowStripPrimitive
open Real Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def primitive (s : ℝ) : ℝ :=
  s * log (2 + sqrt (s^2+4)) - s * log s + 2 * arsinh (s/2)

theorem radical_reciprocal (s : ℝ) (hs : 0 < s) :
    sqrt (1+(2/s)^2) = sqrt (s^2+4)/s := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp
  <;> ring

theorem radical_half (s : ℝ) :
    sqrt (1+(s/2)^2) = sqrt (s^2+4)/2 := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  rw [div_pow, Real.sq_sqrt (by positivity)]
  ring

theorem arsinh_reciprocal (s : ℝ) (hs : 0 < s) :
    arsinh (2/s) = log (2+sqrt (s^2+4))-log s := by
  rw [Real.arsinh, radical_reciprocal s hs,
    show 2/s+sqrt (s^2+4)/s = (2+sqrt (s^2+4))/s by ring,
    Real.log_div (by positivity) hs.ne']

theorem primitive_eq_arsinh (s : ℝ) (hs : 0 < s) :
    primitive s = s*arsinh (2/s)+2*arsinh (s/2) := by
  rw [arsinh_reciprocal s hs]
  unfold primitive
  ring

theorem primitive_derivative (s : ℝ) (hs : 0 < s) :
    HasDerivAt primitive (arsinh (2/s)) s := by
  have h1 := ((hasDerivAt_const s (2 : ℝ)).div (hasDerivAt_id s) hs.ne').arsinh
  have h2 := ((hasDerivAt_id s).div_const 2).arsinh
  have hd : HasDerivAt (fun t : ℝ => t*arsinh (2/t)+2*arsinh (t/2))
      (arsinh (2/s)) s := by
    dsimp at h1 h2
    convert! ((hasDerivAt_id s).mul h1).add (h2.const_mul 2) using 1
    rw [radical_reciprocal s hs, radical_half s]
    field_simp [hs.ne', show sqrt (s^2+4) ≠ 0 by positivity]
    <;> ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hs] with t ht
  exact primitive_eq_arsinh t ht

theorem primitive_zero : primitive 0 = 0 := by simp [primitive]

theorem primitive_continuousAt_zero : ContinuousAt primitive 0 := by
  unfold primitive
  apply ContinuousAt.add
  · apply ContinuousAt.sub
    · apply ContinuousAt.mul (by fun_prop)
      apply ContinuousAt.log (by fun_prop)
      positivity
    · exact Real.continuous_mul_log.continuousAt
  · fun_prop

theorem primitive_tendsto_zero : Tendsto primitive (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [← primitive_zero]
  exact primitive_continuousAt_zero.tendsto.mono_left nhdsWithin_le_nhds

theorem arsinh_three_quarters : arsinh (3/4 : ℝ) = log 2 := by
  have hs : sqrt (1+(3/4 : ℝ)^2) = 5/4 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  rw [Real.arsinh, hs]
  norm_num

theorem arsinh_four_thirds : arsinh (4/3 : ℝ) = log 3 := by
  have hs : sqrt (1+(4/3 : ℝ)^2) = 5/3 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  rw [Real.arsinh, hs]
  norm_num

theorem primitive_eight_thirds :
    primitive (8/3) = (8/3)*log 2+2*log 3 := by
  rw [primitive_eq_arsinh _ (by norm_num)]
  norm_num only [show (2 / (8/3 : ℝ)) = 3/4 by norm_num,
    show ((8/3 : ℝ)/2) = 4/3 by norm_num]
  rw [arsinh_three_quarters, arsinh_four_thirds]

#print axioms primitive_derivative
#print axioms primitive_tendsto_zero
#print axioms primitive_eight_thirds
end
end Gebendorfer.RadenkovicGutman.LowStripPrimitive
