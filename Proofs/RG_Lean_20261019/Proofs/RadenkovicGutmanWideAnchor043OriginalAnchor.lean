/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor043Origin
import Proofs.RadenkovicGutmanWideAnchor043FinitePayment
import Proofs.RadenkovicGutmanWideAnchor043PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor043OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2181155808649002338633350998267585/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[43]?=some (⟨52,10,22,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor043Origin.payment+WideAnchor043FinitePayment.payment+WideAnchor043PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+22+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 22 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor043Origin.payment WideAnchor043FinitePayment.payment WideAnchor043PositiveTail.payment 10 22
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor043Origin.actual_integral G u hN)
    (WideAnchor043FinitePayment.actual_integral G u hd)
    (WideAnchor043PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+22+10+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 22 10 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor043Origin.payment WideAnchor043FinitePayment.payment WideAnchor043PositiveTail.payment 22 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor043Origin.actual_integral_swapped G u hN)
    (WideAnchor043FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor043PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor043OriginalAnchor
