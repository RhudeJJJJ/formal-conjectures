/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanReducedEscapeForms
namespace Gebendorfer.RadenkovicGutman.ReducedEscapeSigns
open Set
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
theorem signs (d : ℝ) (hd : 46 ≤ d) : CorrelatedEscape.Signs d := by
  have hd0 : 0 < d := by linarith only [hd]
  have hh : 1/d ∈ Ioc (0 : ℝ) (1/46) := by
    refine ⟨by positivity,?_⟩
    apply (div_le_div_iff₀ hd0 (by norm_num : (0 : ℝ) < 46)).mpr
    linarith only [hd]
  intro x hx a ha b hb
  have hx0 : 0 < x := by linarith only [hx.1]
  have hS := ReducedEscapeForms.directedCore_nonneg (1/d) x a b hh hx ha hb
  have hR := ReducedEscapeForms.reserveInner_nonneg (1/d) x a b hh hx ha hb
  have h1 : 1/(1/d)=d := by field_simp [hd0.ne']
  have h2 : x/(1/d)=d*x := by field_simp [hd0.ne']
  have h3 (a : ℝ) : a*(1/d)/x=a/(d*x) := by field_simp [hd0.ne',hx0.ne']
  rw [h1,h2,h3 a,h3 b] at hS hR
  have hy0 : 0 < d*x := mul_pos hd0 hx0
  have hP : d*x ≤ d*x+a/(d*x) := le_add_of_nonneg_right (div_nonneg ha.1 hy0.le)
  have hQ : d*x ≤ d*x+b/(d*x) := le_add_of_nonneg_right (div_nonneg hb.1 hy0.le)
  have hL : CorrelatedEscapeReduction.factorLead (d*x) (d*x+a/(d*x)) (d*x+b/(d*x))
      (CorrelatedEscape.payment d x) ≤ 0 := by
    rw [← CorrelatedEscapeReduction.lead_factor]
    exact (CorrelatedEscape.lead_neg _ _ _ _ hy0 hP hQ (CorrelatedEscape.payment_range d x hd)).le
  constructor
  · rw [EscapeFactorSigns.directed_identity]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hL) hS
  · rw [EscapeFactorSigns.reserve_identity]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hR
#print axioms signs
end
end Gebendorfer.RadenkovicGutman.ReducedEscapeSigns
