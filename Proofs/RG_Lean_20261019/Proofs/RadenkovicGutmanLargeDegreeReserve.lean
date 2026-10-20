/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanOriginalAssembly
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The actual degree-46 numerical reserve

Source: the revised universal manuscript and
`other_degrees/source/rg_multiarm_large_degree_integral_certificate.py`,
with cutoff 46, XLO = 653/2000 and PAYMENT = 21/25.

This proves the closed transcendental reserve, without importing Python
interval endpoints or assuming a positive numerical margin. The missing
pointwise polynomial certificates and the integral-to-primitive identity
remain separate obligations. In particular this module does not inhabit
`OriginalAssembly.Inputs.degreeGeFortysix`.
-/
namespace Gebendorfer.RadenkovicGutman.LargeDegreeReserve
open Real Set
open scoped Classical
noncomputable section

def atanLower (x : ℝ) : ℝ := x - x ^ 3 / 3
def atanUpper (x : ℝ) : ℝ := x - x ^ 3 / 3 + x ^ 5 / 5

theorem atan_lower (x : ℝ) (hx : 0 ≤ x) : atanLower x ≤ arctan x := by
  have hd (y : ℝ) : HasDerivAt (fun z => arctan z - atanLower z)
      (y ^ 4 / (1 + y ^ 2)) y := by
    have h := (hasDerivAt_arctan y).sub
      ((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 3).div_const 3))
    simp only [id_eq] at h
    convert h using 1 <;> first
      | rfl
      | (field_simp [show 1+y^2 ≠ 0 by positivity]; ring)
  have hm := monotone_of_hasDerivAt_nonneg hd (by intro y; positivity)
  have h := hm hx
  norm_num [atanLower] at h
  dsimp [atanLower]
  linarith only [h]

theorem atan_upper (x : ℝ) (hx : 0 ≤ x) : arctan x ≤ atanUpper x := by
  have hd (y : ℝ) : HasDerivAt (fun z => atanUpper z - arctan z)
      (y ^ 6 / (1 + y ^ 2)) y := by
    have h := (((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 3).div_const 3)).add
      (((hasDerivAt_id y).pow 5).div_const 5)).sub (hasDerivAt_arctan y)
    simp only [id_eq] at h
    convert h using 1 <;> first
      | rfl
      | (field_simp [show 1+y^2 ≠ 0 by positivity]; ring)
  have hm := monotone_of_hasDerivAt_nonneg hd (by intro y; positivity)
  have h := hm hx
  norm_num [atanUpper] at h
  dsimp [atanUpper]
  linarith only [h]

theorem atan_le_self (x : ℝ) (hx : 0 ≤ x) : arctan x ≤ x := by
  have hd (y : ℝ) : HasDerivAt (fun z => z - arctan z)
      (y ^ 2 / (1 + y ^ 2)) y := by
    convert (hasDerivAt_id y).sub (hasDerivAt_arctan y) using 1 <;> first
      | rfl
      | (field_simp [show 1+y^2 ≠ 0 by positivity]; ring)
  have hm := monotone_of_hasDerivAt_nonneg hd (by intro y; positivity)
  have h := hm hx
  norm_num at h
  linarith only [h]

theorem log_two_upper : log 2 ≤ (69315 / 100000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) 6
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem log_three_upper : log 3 ≤ (109862 / 100000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1) 10
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem log_small_lower : (19 / 40 : ℝ) ≤ log (4021 / 2500 : ℝ) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1521/6521)
    (by norm_num : (1521/6521 : ℝ) < 1) 4
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

def tailParameter (y : ℝ) : ℝ := (sqrt (y ^ 2 + 4) - y) / 2

/-- The original tail primitive, not an asserted value of an integral. -/
def tailPrimitive (y : ℝ) : ℝ :=
  let t := tailParameter y;
  -((t - 1/t) * log (1 + t ^ 2) - 2*t + 4*arctan t) / 2

theorem tail_parameter_properties (y : ℝ) (hy : 0 ≤ y) :
    0 < tailParameter y ∧ tailParameter y ≤ 1 ∧
      (tailParameter y) ^ 2 + y * tailParameter y = 1 := by
  have hs := Real.sq_sqrt (show 0 ≤ y^2+4 by positivity)
  have hn := Real.sqrt_nonneg (y^2+4)
  have ht : 0 < tailParameter y := by unfold tailParameter; nlinarith
  have he : (tailParameter y)^2 + y * tailParameter y = 1 := by
    unfold tailParameter
    nlinarith
  refine ⟨ht, ?_, he⟩
  nlinarith [mul_nonneg hy ht.le]

theorem tail_lower (y : ℝ) (hy : 0 ≤ y) : -tailParameter y ≤ tailPrimitive y := by
  obtain ⟨ht, ht1, _⟩ := tail_parameter_properties y hy
  have hc : tailParameter y - 1 / tailParameter y ≤ 0 := by
    have hs : (tailParameter y)^2 ≤ 1 := by nlinarith
    have h : tailParameter y ≤ 1/tailParameter y :=
      (le_div_iff₀ ht).mpr (by nlinarith)
    nlinarith
  have hl : 0 ≤ log (1 + (tailParameter y)^2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (tailParameter y)])
  have hm := mul_nonpos_of_nonpos_of_nonneg hc hl
  have ha := atan_le_self (tailParameter y) ht.le
  unfold tailPrimitive
  linarith only [hm, ha]

theorem far_tail_lower : -(1 / 460 : ℝ) ≤ tailPrimitive 460 := by
  obtain ⟨ht, _, he⟩ := tail_parameter_properties 460 (by norm_num)
  have hb : tailParameter 460 ≤ (1/460 : ℝ) := by nlinarith [sq_nonneg (tailParameter 460)]
  linarith [tail_lower 460 (by norm_num)]

theorem half_parameter_bounds :
    (78077 / 100000 : ℝ) ≤ tailParameter (1/2) ∧
      tailParameter (1/2) ≤ (78078 / 100000 : ℝ) := by
  have hs := Real.sq_sqrt (show 0 ≤ (1/2 : ℝ)^2+4 by norm_num)
  have hn := Real.sqrt_nonneg ((1/2 : ℝ)^2+4)
  unfold tailParameter
  constructor <;> nlinarith

theorem half_log_lower : (19/40 : ℝ) ≤ log (1 + (tailParameter (1/2))^2) := by
  have ht := half_parameter_bounds.1
  have ht0 := (tail_parameter_properties (1/2) (by norm_num)).1
  have hb : (4021/2500 : ℝ) ≤ 1 + (tailParameter (1/2))^2 := by nlinarith
  exact log_small_lower.trans (Real.log_le_log (by norm_num) hb)

theorem half_angle :
    arctan (tailParameter (1/2)) +
      arctan ((1-tailParameter (1/2))/(1+tailParameter (1/2))) = Real.pi/4 := by
  let t := tailParameter (1/2)
  have ht : 0 < t := (tail_parameter_properties (1/2) (by norm_num)).1
  have hd : 0 < 1+t := by positivity
  have hp : t * ((1-t)/(1+t)) < 1 := by
    rw [← mul_div_assoc]
    apply (div_lt_one hd).mpr
    nlinarith [sq_nonneg t]
  have he : (t+(1-t)/(1+t))/(1-t*((1-t)/(1+t))) = 1 := by
    field_simp [ne_of_gt hd, ne_of_gt (sub_pos.mpr hp), show 1+t^2 ≠ 0 by positivity]
    <;> ring_nf <;> field_simp [show 1+t^2 ≠ 0 by positivity] <;> ring
  have h := Real.arctan_add hp
  rw [he, Real.arctan_one] at h
  exact h

theorem half_tail_lower :
    (78077/100000 : ℝ) + (19/160 : ℝ) - Real.pi/2 +
      2 * atanLower (1231/10000) ≤ tailPrimitive (1/2) := by
  let t := tailParameter (1/2)
  obtain ⟨ht, _, hq⟩ := tail_parameter_properties (1/2) (by norm_num)
  have hc : t - 1/t = -(1/2 : ℝ) := by
    dsimp [t]
    field_simp [ht.ne']
    nlinarith [hq]
  have hu : (1231/10000 : ℝ) ≤ (1-t)/(1+t) := by
    apply (le_div_iff₀ (by positivity : 0 < 1+t)).mpr
    have hb := half_parameter_bounds.2
    change t ≤ _ at hb
    linarith
  have ha := (atan_lower (1231/10000) (by norm_num)).trans
    (Real.arctan_le_arctan_iff.mpr hu)
  have he : tailPrimitive (1/2) = t + log (1+t^2)/4 - 2*arctan t := by
    change -((t-1/t)*log (1+t^2)-2*t+4*arctan t)/2 = _
    rw [hc]
    ring
  have hang := half_angle
  have hb := half_parameter_bounds.1
  have hl := half_log_lower
  rw [he]
  change arctan t + arctan ((1-t)/(1+t)) = _ at hang
  change _ ≤ t at hb
  change _ ≤ log (1+t^2) at hl
  linarith only [ha, hang, hb, hl]

def reserve : ℝ :=
  (-(8/3 : ℝ)*log 2 - 2*log 3 + 2/(5*(653/2000 : ℝ)))/46 - log 2/2 +
    tailPrimitive (1/2) + (21/25 : ℝ)*(arctan 10 - arctan (653/2000)) + tailPrimitive 460

theorem reserve_transport_paid : (2/47 : ℝ) < reserve / Real.pi := by
  have hp : Real.pi < (22/7 : ℝ) := lt_trans Real.pi_lt_d4 (by norm_num)
  have h10 : arctan (10 : ℝ) = Real.pi/2 - arctan (1/10 : ℝ) := by
    simpa using Real.arctan_inv_of_pos (x := (1/10 : ℝ)) (by norm_num)
  have h1 := atan_upper (1/10) (by norm_num)
  have h2 := atan_upper (653/2000) (by norm_num)
  have hj := half_tail_lower
  have hf := far_tail_lower
  have hl2 := log_two_upper
  have hl3 := log_three_upper
  apply (lt_div_iff₀ Real.pi_pos).mpr
  unfold reserve
  norm_num [atanLower, atanUpper] at h1 h2 hj
  linarith only [hp, h10, h1, h2, hj, hf, hl2, hl3]

theorem reserve_positive : 0 < reserve := by
  have h := (lt_div_iff₀ Real.pi_pos).mp reserve_transport_paid
  exact lt_trans (by positivity) h

def coefficient : ℝ := -(8/3 : ℝ)*log 2 - 2*log 3 + 2/(5*(653/2000 : ℝ))
def coefficientLower : ℝ :=
  -(8/3 : ℝ)*(69315/100000) - 2*(109862/100000) + 2/(5*(653/2000 : ℝ))

theorem coefficient_uniform (d : ℝ) (hd : 46 ≤ d) :
    coefficientLower / 46 ≤ coefficient / d := by
  have hd0 : 0 < d := by linarith
  have hc : coefficientLower ≤ coefficient := by
    unfold coefficientLower coefficient
    linarith [log_two_upper, log_three_upper]
  have hn : coefficientLower ≤ 0 := by norm_num [coefficientLower]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 46) hd0).mpr
  calc
    coefficientLower * d ≤ coefficientLower * 46 := mul_le_mul_of_nonpos_left hd hn
    _ ≤ coefficient * 46 := mul_le_mul_of_nonneg_right hc (by norm_num)

theorem far_tail_uniform (d : ℝ) (hd : 46 ≤ d) :
    -(1/460 : ℝ) ≤ tailPrimitive (10*d) := by
  have hy : 0 ≤ 10*d := by linarith
  obtain ⟨ht, _, he⟩ := tail_parameter_properties (10*d) hy
  have hm := mul_le_mul_of_nonneg_right (show (460 : ℝ) ≤ 10*d by linarith) ht.le
  have hb : tailParameter (10*d) ≤ (1/460 : ℝ) := by
    nlinarith [sq_nonneg (tailParameter (10*d))]
  linarith [tail_lower (10*d) hy]

/-- The original degree-dependent closed expression, for all real d >= 46. -/
def reserveAt (d : ℝ) : ℝ :=
  coefficient/d - log 2/2 + tailPrimitive (1/2) +
    (21/25 : ℝ)*(arctan 10 - arctan (653/2000)) + tailPrimitive (10*d)

theorem uniform_transport_paid (d : ℝ) (hd : 46 ≤ d) :
    (2/47 : ℝ) < reserveAt d / Real.pi := by
  have hp : Real.pi < (22/7 : ℝ) := lt_trans Real.pi_lt_d4 (by norm_num)
  have h10 : arctan (10 : ℝ) = Real.pi/2 - arctan (1/10 : ℝ) := by
    simpa using Real.arctan_inv_of_pos (x := (1/10 : ℝ)) (by norm_num)
  have h1 := atan_upper (1/10) (by norm_num)
  have h2 := atan_upper (653/2000) (by norm_num)
  have hj := half_tail_lower
  have hf := far_tail_uniform d hd
  have hc := coefficient_uniform d hd
  have hl2 := log_two_upper
  apply (lt_div_iff₀ Real.pi_pos).mpr
  unfold reserveAt
  norm_num [atanLower, atanUpper] at h1 h2 hj
  norm_num [coefficientLower] at hc
  linarith only [hp, h10, h1, h2, hj, hf, hc, hl2]

/-- Only the actual graph-integral comparison remains as a premise here.
This premise still requires the original polynomial and integration proofs. -/
theorem strict_fusion_of_original_integral_bound {m : ℕ} (C : SimpleGraph (Fin m))
    (u : Fin m) (p q : ℕ) (hT : (CoreQuotient.source C u p q).IsTree)
    (hd : 46 ≤ C.degree u)
    (hI : reserveAt (C.degree u) / Real.pi ≤
      ActualFusionIntegral.normalizedIntegral C u p q 2) :
    laplacianEnergy (CoreQuotient.fused C u p q) <
      laplacianEnergy (CoreQuotient.source C u p q) := by
  have hn := OriginalAssembly.source_order_ge_degree_add_three C u p q
  apply OriginalAssembly.strict_of_cutoff_reserve C u p q 47 hT (by omega)
    (by omega) (by omega)
  exact lt_of_lt_of_le (uniform_transport_paid _ (by exact_mod_cast hd)) hI

#print axioms atan_lower
#print axioms atan_upper
#print axioms atan_le_self
#print axioms log_two_upper
#print axioms log_three_upper
#print axioms log_small_lower
#print axioms tail_parameter_properties
#print axioms tail_lower
#print axioms far_tail_lower
#print axioms half_parameter_bounds
#print axioms half_log_lower
#print axioms half_angle
#print axioms half_tail_lower
#print axioms reserve_transport_paid
#print axioms reserve_positive
#print axioms coefficient_uniform
#print axioms far_tail_uniform
#print axioms uniform_transport_paid
#print axioms strict_fusion_of_original_integral_bound
end
end Gebendorfer.RadenkovicGutman.LargeDegreeReserve
