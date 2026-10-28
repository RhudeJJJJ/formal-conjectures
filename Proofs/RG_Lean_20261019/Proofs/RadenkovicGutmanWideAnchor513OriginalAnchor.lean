/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor513Origin
import Proofs.RadenkovicGutmanWideAnchor513FinitePayment
import Proofs.RadenkovicGutmanWideAnchor513PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor513OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2586815308517612041464138522479713/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[513]?=some (⟨52,4,43,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor513Origin.payment+WideAnchor513FinitePayment.payment+WideAnchor513PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+43+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 43 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor513Origin.payment WideAnchor513FinitePayment.payment WideAnchor513PositiveTail.payment 4 43
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor513Origin.actual_integral G u hN)
    (WideAnchor513FinitePayment.actual_integral G u hd)
    (WideAnchor513PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+43+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 43 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor513Origin.payment WideAnchor513FinitePayment.payment WideAnchor513PositiveTail.payment 43 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor513Origin.actual_integral_swapped G u hN)
    (WideAnchor513FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor513PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor513OriginalAnchor
