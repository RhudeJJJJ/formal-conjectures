/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor034Origin
import Proofs.RadenkovicGutmanWideAnchor034FinitePayment
import Proofs.RadenkovicGutmanWideAnchor034PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor034OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (39252063946289937773687788873763/393062208820009069919698461753344)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[34]?=some (⟨52,10,13,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor034Origin.payment+WideAnchor034FinitePayment.payment+WideAnchor034PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+13+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 13 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor034Origin.payment WideAnchor034FinitePayment.payment WideAnchor034PositiveTail.payment 10 13
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor034Origin.actual_integral G u hN)
    (WideAnchor034FinitePayment.actual_integral G u hd)
    (WideAnchor034PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+13+10+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 13 10 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor034Origin.payment WideAnchor034FinitePayment.payment WideAnchor034PositiveTail.payment 13 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor034Origin.actual_integral_swapped G u hN)
    (WideAnchor034FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor034PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor034OriginalAnchor
