/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripGeometry

/-! The original constant-strip target norm quotient >=1/2.
Source: rg_multiarm_small_ordinate_midstrip.py, build_laurent_conditions.
The original outside/directed/full-reserve signs remain hypotheses. -/
namespace Gebendorfer.RadenkovicGutman.LowStripConstantGeometry
open Focus LowStripGeometry Set CoreQuotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem lead_pos (y P Q : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q) :
    0 < lead y P Q 1 := by
  have hb := Complex.normSq_pos.mpr (Focus.B_ne_zero y P Q hy hP hQ)
  have hh := (le_div_iff₀ hb).mp (TailHalfGeometry.infinity_ratio_ge_half y P Q hy hP hQ)
  unfold lead
  norm_num
  nlinarith only [hh,hb]

theorem log_lower_of_signs (d y P Q : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q)
    (hO : 0 ≤ outside d y P Q 1) (hD : 0 ≤ directed d y P Q 1)
    (hR : 0 ≤ reserve d y P Q 1) (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    -Real.log 2 ≤ Real.log ‖quotient y P Q ζ‖ := by
  have hr : 0 ≤ r d y := by unfold r; positivity
  have hH := QuadraticDisk.convex_nonneg _ _ _ _ _ _ (lead_pos y P Q hy hP hQ)
    hr hO hD hR ζ hζ
  rw [← LowStripGeometry.quadratic_identity] at hH
  norm_num at hH
  have hb := Complex.normSq_pos.mpr (TailHalfGeometry.denominator_ne_zero d y P Q hy hP hQ ζ hζ)
  have hs : (1/2 : ℝ)^2 ≤ ‖quotient y P Q ζ‖^2 := by
    rw [quotient,norm_div]
    simp only [div_pow,← Complex.normSq_eq_norm_sq]
    apply (le_div_iff₀ hb).mpr
    norm_num
    nlinarith only [hH]
  have hn := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1/2)
    (norm_nonneg (quotient y P Q ζ))).mp hs
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) hn
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),Real.log_one,zero_sub] at hl
  exact hl

attribute [-instance] SimpleGraph.fintypeEdgeSetSup

theorem graph_lower_of_actual_signs {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (y : ℝ) (hy : 0 < y)
    (hO : 0 ≤ outside (C.degree u) y (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) 1)
    (hD : 0 ≤ directed (C.degree u) y (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) 1)
    (hR : 0 ≤ reserve (C.degree u) y (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) 1) :
    -Real.log 2 ≤ MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  have hp := div_nonneg (PathEnclosure.arm_nonneg y p) hy.le
  have hq := div_nonneg (PathEnclosure.arm_nonneg y q) hy.le
  have h := log_lower_of_signs (C.degree u) y _ _ (by positivity) hy
    (by linarith only [hp]) (by linarith only [hq]) hO hD hR _ (schur_in_disk C u y hy).1
  change -Real.log 2 ≤ Real.log ‖(shifted (z y) (source C u p q)).det /
    (shifted (z y) (fused C u p q)).det‖
  rw [concrete_graph_quotient C u y hy p q]
  exact h

#print axioms lead_pos
#print axioms log_lower_of_signs
#print axioms graph_lower_of_actual_signs
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.LowStripConstantGeometry
