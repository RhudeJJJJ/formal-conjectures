/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor258Origin
import Proofs.RadenkovicGutmanWideAnchor258FinitePayment
import Proofs.RadenkovicGutmanWideAnchor258PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor258OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3150364769823387637583006037265265/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[258]?=some (⟨52,0,35,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor258Origin.payment+WideAnchor258FinitePayment.payment+WideAnchor258PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+35+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 35 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor258Origin.payment WideAnchor258FinitePayment.payment WideAnchor258PositiveTail.payment 0 35
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor258Origin.actual_integral G u hN)
    (WideAnchor258FinitePayment.actual_integral G u hd)
    (WideAnchor258PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+35+0+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 35 0 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor258Origin.payment WideAnchor258FinitePayment.payment WideAnchor258PositiveTail.payment 35 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor258Origin.actual_integral_swapped G u hN)
    (WideAnchor258FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor258PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor258OriginalAnchor
