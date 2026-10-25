/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor035Origin
import Proofs.RadenkovicGutmanWideAnchor035FinitePayment
import Proofs.RadenkovicGutmanWideAnchor035PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor035OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1971032762149181392055880507462193/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[35]?=some (⟨52,10,14,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor035Origin.payment+WideAnchor035FinitePayment.payment+WideAnchor035PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+14+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 14 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor035Origin.payment WideAnchor035FinitePayment.payment WideAnchor035PositiveTail.payment 10 14
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor035Origin.actual_integral G u hN)
    (WideAnchor035FinitePayment.actual_integral G u hd)
    (WideAnchor035PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+14+10+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 14 10 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor035Origin.payment WideAnchor035FinitePayment.payment WideAnchor035PositiveTail.payment 14 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor035Origin.actual_integral_swapped G u hN)
    (WideAnchor035FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor035PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor035OriginalAnchor
