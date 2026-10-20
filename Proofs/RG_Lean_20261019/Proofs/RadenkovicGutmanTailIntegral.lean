/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLargeDegreeReserve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact original tail integral and its payments

Source: revised universal manuscript, equations (other-17)--(other-20).
The same t(y) and J(y) as in the original degree-46 certificate are used.
The graph-to-tail polynomial inequalities remain separate obligations.
-/
namespace Gebendorfer.RadenkovicGutman.TailIntegral
open Real Set Filter MeasureTheory LargeDegreeReserve
open scoped Topology Classical
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
  simp only [id_eq] at h
  convert h using 1 <;> first
    | rfl
    | (field_simp [ht.ne', show 1+t^2 ≠ 0 by positivity]; ring)

theorem tail_parameter_derivative (y : ℝ) :
    HasDerivAt tailParameter (-tailParameter y / sqrt (y^2+4)) y := by
  have hs : 0 < sqrt (y^2+4) := Real.sqrt_pos.mpr (by positivity)
  have h := (((((hasDerivAt_id y).pow 2).add_const 4).sqrt hs.ne').sub
    (hasDerivAt_id y)).div_const 2
  simp only [id_eq] at h
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
      _ = 1 := by rw [hts]; exact div_self (by positivity)
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

theorem positive_tail_lower (y : ℝ) (hy : 4 ≤ y) :
    (2/5 : ℝ)/y^2 ≤ positiveTail y := by
  let t := tailParameter y
  have hy0 : 0 < y := by linarith
  obtain ⟨ht,_,hq⟩ := tail_parameter_properties y hy0.le
  have hm := mul_le_mul_of_nonneg_right hy ht.le
  have hb : t ≤ (1/4 : ℝ) := by nlinarith [sq_nonneg t]
  have hs : t^2 ≤ (1/16 : ℝ) := by nlinarith
  have he : y*t=1-t^2 := by linarith [hq]
  have he2 := congrArg (fun z : ℝ => z^2) he
  have hf : (4/5 : ℝ)/y^2 ≤ t^2/(1+t^2) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hy0) (by positivity : 0 < 1+t^2)).mpr
    nlinarith [sq_nonneg (t^2)]
  have hl := Real.one_sub_inv_le_log_of_pos (show 0 < 1+t^2 by positivity)
  have hr : 1-(1+t^2)⁻¹=t^2/(1+t^2) := by
    field_simp [show 1+t^2 ≠ 0 by positivity]; ring
  rw [hr] at hl
  change (2/5 : ℝ)/y^2 ≤ log (1+t^2)/2
  linarith only [hf,hl]

theorem tail_gain (Y : ℝ) (hY : 4 ≤ Y) : (2/(5*Y) : ℝ) ≤ -tailPrimitive Y := by
  have hY0 : 0 < Y := by linarith
  have h := integral_mono_ae
    (inv_square_integrable_integral (2/5) Y (by norm_num) hY0).1
    (positive_tail_integrable Y hY0)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact positive_tail_lower y (by linarith))
  rw [positive_tail_integral Y hY0,
    (inv_square_integrable_integral (2/5) Y (by norm_num) hY0).2] at h
  convert h using 1 <;> ring

theorem escape_start_gain (d : ℝ) (hd : 46 ≤ d) :
    (2/(5*(653/2000 : ℝ)))/d ≤ -tailPrimitive ((653/2000)*d) := by
  have h := tail_gain ((653/2000)*d) (by linarith)
  convert h using 1 <;> ring

theorem tail_cost_1024 : -(1/2048 : ℝ) ≤ tailPrimitive 1024 := by
  convert tail_cost 1024 (by norm_num) using 1 <;> norm_num

def escapeDensity (d y : ℝ) : ℝ := (21/25 : ℝ)/(d*(1+(y/d)^2))

/-- Exact payment for the original scaled escape region. -/
theorem escape_integral (d : ℝ) (hd : 0 < d) :
    (∫ y : ℝ in ((653/2000)*d)..(10*d), escapeDensity d y) =
      (21/25 : ℝ)*(arctan 10 - arctan (653/2000)) := by
  let F : ℝ → ℝ := fun y => (21/25 : ℝ)*arctan (y/d)
  have hf (y : ℝ) : HasDerivAt F (escapeDensity d y) y := by
    have h := ((hasDerivAt_id y).div_const d).arctan.const_mul (21/25 : ℝ)
    convert h using 1 <;> first
      | rfl
      | (dsimp [escapeDensity]; field_simp [hd.ne',show 1+(y/d)^2 ≠ 0 by positivity]; ring)
  have hc : Continuous (fun y : ℝ => d*(1+(y/d)^2)) := by fun_prop
  have hg : Continuous (escapeDensity d) :=
    continuous_const.div hc (fun y => by positivity)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hf y)
    (hg.intervalIntegrable ((653/2000)*d) (10*d))
  have h10 : (10*d)/d=(10 : ℝ) := by field_simp [hd.ne']
  have hlo : ((653/2000 : ℝ)*d)/d=653/2000 := by field_simp [hd.ne']
  simpa only [F,h10,hlo,mul_sub] using h

theorem phi_interval_integral (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ y : ℝ in a..b, phi y) = tailPrimitive a - tailPrimitive b := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi (phi_integrable a ha) hab
  rw [phi_integral a ha, phi_integral b (lt_of_lt_of_le ha hab)] at h
  exact h.symm

theorem interval_integrable_of_Ioi {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact hf.mono_set (by intro y hy; exact lt_of_le_of_lt ha hy.1)

theorem escape_continuous (d : ℝ) (hd : 0 < d) : Continuous (escapeDensity d) := by
  have hc : Continuous (fun y : ℝ => d*(1+(y/d)^2)) := by fun_prop
  exact continuous_const.div hc (fun y => by positivity)

/-- Assemble the four original, gap-free regions. The graph bounds are inputs;
all scalar integration and the original tail gain are discharged here. -/
theorem four_region_lower (f : ℝ → ℝ) (d : ℝ) (hd : 46 ≤ d)
    (hf : IntegrableOn f (Ioi 0))
    (hlow : (-(8/3 : ℝ)*log 2-2*log 3)/d-log 2/2 ≤ ∫ y : ℝ in (0 : ℝ)..(1/2), f y)
    (hmiddle : ∀ y ∈ Icc (1/2 : ℝ) ((653/2000)*d), phi y ≤ f y)
    (hescape : ∀ y ∈ Icc ((653/2000 : ℝ)*d) (10*d), escapeDensity d y ≤ f y)
    (htail : ∀ y ∈ Ioi (10*d), phi y ≤ f y) :
    reserveAt d ≤ ∫ y : ℝ in Ioi 0, f y := by
  have hd0 : 0 < d := by linarith
  have ha : (0 : ℝ) ≤ 1/2 := by norm_num
  have hab : (1/2 : ℝ) ≤ (653/2000)*d := by linarith
  have hbc : (653/2000 : ℝ)*d ≤ 10*d := by linarith
  have hb0 : 0 ≤ (653/2000 : ℝ)*d := by positivity
  have hc0 : 0 < 10*d := by positivity
  have hfa := hf.mono_set (Ioi_subset_Ioi ha)
  have hfb := hf.mono_set (Ioi_subset_Ioi hb0)
  have hfc := hf.mono_set (Ioi_subset_Ioi hc0.le)
  have hpab : IntervalIntegrable phi volume (1/2) ((653/2000)*d) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    exact (phi_integrable (1/2) (by norm_num)).mono_set Ioc_subset_Ioi_self
  have hm := intervalIntegral.integral_mono_on hab hpab
    (interval_integrable_of_Ioi hf ha hab) hmiddle
  rw [phi_interval_integral (1/2) _ (by norm_num) hab] at hm
  have he := intervalIntegral.integral_mono_on hbc
    ((escape_continuous d hd0).intervalIntegrable _ _)
    (interval_integrable_of_Ioi hf hb0 hbc) hescape
  rw [escape_integral d hd0] at he
  have ht := integral_mono_ae (phi_integrable (10*d) hc0) hfc (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact htail y hy)
  rw [phi_integral (10*d) hc0] at ht
  have h1 := intervalIntegral.integral_Ioi_sub_Ioi hf ha
  have h2 := intervalIntegral.integral_Ioi_sub_Ioi hfa hab
  have h3 := intervalIntegral.integral_Ioi_sub_Ioi hfb hbc
  have hg := escape_start_gain d hd
  unfold reserveAt coefficient
  rw [add_div]
  linarith only [hlow,hm,he,ht,h1,h2,h3,hg]

/-- Conditional actual-graph endpoint. The remaining premises are the original
low-strip bound and three pointwise graph-to-envelope comparisons. -/
theorem strict_fusion_of_four_regions {m : ℕ} (C : SimpleGraph (Fin m))
    (u : Fin m) (p q : ℕ) (hT : (CoreQuotient.source C u p q).IsTree)
    (hd : 46 ≤ C.degree u)
    (hlow : (-(8/3 : ℝ)*log 2-2*log 3)/(C.degree u : ℝ)-log 2/2 ≤
      ∫ y : ℝ in (0 : ℝ)..(1/2),
        MixedGraphIntegral.logarithm (CoreQuotient.source C u p q) (CoreQuotient.fused C u p q) 2 y)
    (hmiddle : ∀ y ∈ Icc (1/2 : ℝ) ((653/2000)*(C.degree u : ℝ)), phi y ≤
      MixedGraphIntegral.logarithm (CoreQuotient.source C u p q) (CoreQuotient.fused C u p q) 2 y)
    (hescape : ∀ y ∈ Icc ((653/2000 : ℝ)*(C.degree u : ℝ)) (10*(C.degree u : ℝ)),
      escapeDensity (C.degree u) y ≤
        MixedGraphIntegral.logarithm (CoreQuotient.source C u p q) (CoreQuotient.fused C u p q) 2 y)
    (htail : ∀ y ∈ Ioi (10*(C.degree u : ℝ)), phi y ≤
      MixedGraphIntegral.logarithm (CoreQuotient.source C u p q) (CoreQuotient.fused C u p q) 2 y) :
    laplacianEnergy (CoreQuotient.fused C u p q) <
      laplacianEnergy (CoreQuotient.source C u p q) := by
  classical
  apply strict_fusion_of_original_integral_bound C u p q hT hd
  have h := four_region_lower _ (C.degree u) (by exact_mod_cast hd)
    (ActualFusionIntegral.logarithm_integrable C u p q 2) hlow hmiddle hescape htail
  change reserveAt (C.degree u) / Real.pi ≤ (1/Real.pi)*_
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left h (show 0 ≤ 1/Real.pi by positivity)

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
#print axioms positive_tail_lower
#print axioms tail_gain
#print axioms escape_start_gain
#print axioms tail_cost_1024
#print axioms escape_integral
#print axioms phi_interval_integral
#print axioms interval_integrable_of_Ioi
#print axioms escape_continuous
#print axioms four_region_lower
#print axioms strict_fusion_of_four_regions
end
end Gebendorfer.RadenkovicGutman.TailIntegral
