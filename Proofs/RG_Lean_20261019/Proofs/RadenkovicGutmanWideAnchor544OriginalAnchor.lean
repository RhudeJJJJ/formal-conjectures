/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor544Origin
import Proofs.RadenkovicGutmanWideAnchor544FinitePayment
import Proofs.RadenkovicGutmanWideAnchor544PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor544OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (45675863192935490190496432493171/393062208820009069919698461753344)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[544]?=some (⟨52,5,22,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor544Origin.payment+WideAnchor544FinitePayment.payment+WideAnchor544PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+5+22+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 5 22 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor544Origin.payment WideAnchor544FinitePayment.payment WideAnchor544PositiveTail.payment 5 22
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor544Origin.actual_integral G u hN)
    (WideAnchor544FinitePayment.actual_integral G u hd)
    (WideAnchor544PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+22+5+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 22 5 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor544Origin.payment WideAnchor544FinitePayment.payment WideAnchor544PositiveTail.payment 22 5
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor544Origin.actual_integral_swapped G u hN)
    (WideAnchor544FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor544PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor544OriginalAnchor
