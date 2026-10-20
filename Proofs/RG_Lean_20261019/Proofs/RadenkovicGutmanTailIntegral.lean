/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLargeDegreeReserve

/-!
# Exact original tail integral and its payments

Source: revised universal manuscript, equations (other-17)--(other-20).
The same t(y) and J(y) as in the original degree-46 certificate are used.
The graph-to-tail polynomial inequalities remain separate obligations.
-/
namespace Gebendorfer.RadenkovicGutman.TailIntegral
open Real Set Filter MeasureTheory LargeDegreeReserve
open scoped Topology
noncomputable section

def positiveTail (y : ℝ) : ℝ := log (1 + (tailParameter y)^2)/2
def phi (y : ℝ) : ℝ := -positiveTail y

theorem positive_tail_nonneg (y : ℝ) : 0 ≤ positiveTail y := by
  unfold positiveTail
  apply div_nonneg
  · exact Real.log_nonneg (by nlinarith [sq_nonneg (tailParameter y)])
  · norm_num

def primitiveInParameter (t : ℝ) : ℝ :=
  -((t - 1/t)*log (1+t^2)-2*t+4*arctan t)/2

theorem parameter_derivative (t : ℝ) (ht : 0 < t) :
    HasDerivAt primitiveInParameter (-(1+1/t^2)*log (1+t^2)/2) t := by
  have hi := (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht.ne'
  have hl := (((hasDerivAt_id t).pow 2).const_add 1).log
    (show 1+t^2 ≠ 0 by positivity)
  have h := (((((hasDerivAt_id t).sub hi).mul hl).sub
    ((hasDerivAt_id t).const_mul 2)).add ((hasDerivAt_arctan t).const_mul 4)).neg.div_const 2
  convert h using 1 <;> first
    | rfl
    | (field_simp [ht.ne', show 1+t^2 ≠ 0 by positivity]; ring)

theorem tail_parameter_derivative (y : ℝ) :
    HasDerivAt tailParameter (-tailParameter y / sqrt (y^2+4)) y := by
  have hs : 0 < sqrt (y^2+4) := Real.sqrt_pos.mpr (by positivity)
  have h := (((((hasDerivAt_id y).pow 2).add_const 4).sqrt hs.ne').sub
    (hasDerivAt_id y)).div_const 2
  convert h using 1 <;> first
    | rfl
    | (dsimp [tailParameter]; field_simp [hs.ne']; ring)

theorem primitive_derivative (y : ℝ) (hy : 0 ≤ y) :
    HasDerivAt tailPrimitive (positiveTail y) y := by
  let t := tailParameter y
  have ht : 0 < t := (tail_parameter_properties y hy).1
  have hq : t^2+y*t=1 := (tail_parameter_properties y hy).2.2
  have hs : 0 < sqrt (y^2+4) := Real.sqrt_pos.mpr (by positivity)
  have he : sqrt (y^2+4)=2*t+y := by dsimp [t,tailParameter]; ring
  have hts : t*sqrt (y^2+4)=1+t^2 := by rw [he]; nlinarith [hq]
  have hm : (1+1/t^2)*t/sqrt (y^2+4)=1 := by
    calc
      _ = (1+t^2)/(t*sqrt (y^2+4)) := by field_simp [ht.ne',hs.ne']; ring
      _ = 1 := by rw [hts]; field_simp
  have h := (parameter_derivative t ht).comp y (tail_parameter_derivative y)
  have hd : (-(1+1/t^2)*log (1+t^2)/2)*(-t/sqrt (y^2+4)) = positiveTail y := by
    change _ = log (1+t^2)/2
    calc
      _ = (log (1+t^2)/2)*((1+1/t^2)*t/sqrt (y^2+4)) := by ring
      _ = _ := by rw [hm,mul_one]
  rw [hd] at h
  exact h

theorem primitive_nonpos (y : ℝ) (hy : 0 ≤ y) : tailPrimitive y ≤ 0 := by
  let t := tailParameter y
  obtain ⟨ht,ht1,_⟩ := tail_parameter_properties y hy
  have hc : 0 ≤ 1/t-t := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hl : log (1+t^2) ≤ t^2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1+t^2 by positivity)
    linarith
  have hm := mul_le_mul_of_nonneg_left hl hc
  have ha := atan_lower t ht.le
  have he : (1/t-t)*t^2 = t-t^3 := by field_simp [ht.ne']; ring
  rw [he] at hm
  have h3 : t^3 ≤ t := by
    have hsq : t^2 ≤ 1 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq ht.le
    nlinarith
  change -((t-1/t)*log (1+t^2)-2*t+4*arctan t)/2 ≤ 0
  dsimp [atanLower] at ha
  nlinarith only [hm,ha,h3,ht]

theorem parameter_tendsto : Tendsto tailParameter atTop (𝓝 0) := by
  have hb : ∀ᶠ y : ℝ in atTop, tailParameter y ≤ 1/y := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hq := (tail_parameter_properties y hy.le).2.2
    apply (le_div_iff₀ hy).mpr
    nlinarith [sq_nonneg (tailParameter y)]
  have hn : ∀ᶠ y : ℝ in atTop, 0 ≤ tailParameter y := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    exact (tail_parameter_properties y hy).1.le
  exact squeeze_zero' hn hb (tendsto_const_nhds.div_atTop tendsto_id)

theorem primitive_tendsto : Tendsto tailPrimitive atTop (𝓝 0) := by
  have hn : ∀ᶠ y : ℝ in atTop, 0 ≤ -tailPrimitive y := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    exact neg_nonneg.mpr (primitive_nonpos y hy)
  have hb : ∀ᶠ y : ℝ in atTop, -tailPrimitive y ≤ tailParameter y := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    linarith [tail_lower y hy]
  have h := (squeeze_zero' hn hb parameter_tendsto).neg
  simpa using h

theorem positive_tail_integrable (Y : ℝ) (hY : 0 < Y) :
    IntegrableOn positiveTail (Ioi Y) :=
  integrableOn_Ioi_deriv_of_nonneg
    (primitive_derivative Y hY.le).continuousAt.continuousWithinAt
    (fun y hy => primitive_derivative y (by linarith : 0 ≤ y))
    (fun y _ => positive_tail_nonneg y) primitive_tendsto

theorem positive_tail_integral (Y : ℝ) (hY : 0 < Y) :
    (∫ y : ℝ in Ioi Y, positiveTail y) = -tailPrimitive Y := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    (primitive_derivative Y hY.le).continuousAt.continuousWithinAt
    (fun y hy => primitive_derivative y (by linarith : 0 ≤ y))
    (fun y _ => positive_tail_nonneg y) primitive_tendsto
  simpa using h

theorem phi_integrable (Y : ℝ) (hY : 0 < Y) : IntegrableOn phi (Ioi Y) :=
  (positive_tail_integrable Y hY).neg

/-- Exact equality with the original improper tail integral. -/
theorem phi_integral (Y : ℝ) (hY : 0 < Y) :
    (∫ y : ℝ in Ioi Y, phi y) = tailPrimitive Y := by
  simp only [phi, integral_neg, positive_tail_integral Y hY, neg_neg]

theorem inv_square_integrable_integral (k Y : ℝ) (hk : 0 ≤ k) (hY : 0 < Y) :
    IntegrableOn (fun y : ℝ => k/y^2) (Ioi Y) ∧
      (∫ y : ℝ in Ioi Y, k/y^2) = k/Y := by
  have hd (y : ℝ) (hy : 0 < y) :
      HasDerivAt (fun z : ℝ => -k/z) (k/y^2) y := by
    convert (hasDerivAt_const y (-k)).div (hasDerivAt_id y) hy.ne' using 1 <;> ring
  have ht : Tendsto (fun y : ℝ => -k/y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine ⟨integrableOn_Ioi_deriv_of_nonneg (hd Y hY).continuousAt.continuousWithinAt
    (fun y hy => hd y (by linarith)) (fun y _ => by positivity) ht, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (hd Y hY).continuousAt.continuousWithinAt
    (fun y hy => hd y (by linarith)) (fun y _ => by positivity) ht
  simpa using h

theorem positive_tail_upper (y : ℝ) (hy : 0 < y) : positiveTail y ≤ (1/2 : ℝ)/y^2 := by
  have ht := (tail_parameter_properties y hy.le).1
  have hq := (tail_parameter_properties y hy.le).2.2
  have hb : tailParameter y ≤ 1/y := (le_div_iff₀ hy).mpr (by nlinarith [sq_nonneg (tailParameter y)])
  have hs := pow_le_pow_left₀ ht.le hb 2
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1+(tailParameter y)^2 by positivity)
  unfold positiveTail
  have he : (1/y)^2 = 1/y^2 := by ring
  rw [he] at hs
  linarith

theorem tail_cost (Y : ℝ) (hY : 0 < Y) : -(1/(2*Y)) ≤ tailPrimitive Y := by
  have h := integral_mono_ae (positive_tail_integrable Y hY)
    (inv_square_integrable_integral (1/2) Y (by norm_num) hY).1
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact positive_tail_upper y (by linarith))
  rw [positive_tail_integral Y hY,
    (inv_square_integrable_integral (1/2) Y (by norm_num) hY).2] at h
  convert neg_le_neg h using 1 <;> ring

#print axioms parameter_derivative
#print axioms tail_parameter_derivative
#print axioms primitive_derivative
#print axioms primitive_nonpos
#print axioms parameter_tendsto
#print axioms primitive_tendsto
#print axioms positive_tail_integrable
#print axioms positive_tail_integral
#print axioms phi_integrable
#print axioms phi_integral
#print axioms inv_square_integrable_integral
#print axioms positive_tail_upper
#print axioms tail_cost
end
end Gebendorfer.RadenkovicGutman.TailIntegral
