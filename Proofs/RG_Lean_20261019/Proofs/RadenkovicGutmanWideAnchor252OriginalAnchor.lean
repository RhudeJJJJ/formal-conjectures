/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor252Origin
import Proofs.RadenkovicGutmanWideAnchor252FinitePayment
import Proofs.RadenkovicGutmanWideAnchor252PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor252OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (38797634214586630032456494297811/393062208820009069919698461753344)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[252]?=some (⟨52,0,29,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor252Origin.payment+WideAnchor252FinitePayment.payment+WideAnchor252PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+29+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 29 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor252Origin.payment WideAnchor252FinitePayment.payment WideAnchor252PositiveTail.payment 0 29
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor252Origin.actual_integral G u hN)
    (WideAnchor252FinitePayment.actual_integral G u hd)
    (WideAnchor252PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+29+0+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 29 0 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor252Origin.payment WideAnchor252FinitePayment.payment WideAnchor252PositiveTail.payment 29 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor252Origin.actual_integral_swapped G u hN)
    (WideAnchor252FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor252PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor252OriginalAnchor
