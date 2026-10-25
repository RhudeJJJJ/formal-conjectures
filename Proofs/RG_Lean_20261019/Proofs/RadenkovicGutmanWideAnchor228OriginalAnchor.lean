/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor228Origin
import Proofs.RadenkovicGutmanWideAnchor228FinitePayment
import Proofs.RadenkovicGutmanWideAnchor228PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor228OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1850538888977064702555936691136841/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[228]?=some (⟨18,0,12,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor228Origin.payment+WideAnchor228FinitePayment.payment+WideAnchor228PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+12+2≤18) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 12 (((17/9) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((17/9)) (1/268435456) 128 target
    WideAnchor228Origin.payment WideAnchor228FinitePayment.payment WideAnchor228PositiveTail.payment 0 12
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor228Origin.actual_integral G u hN)
    (WideAnchor228FinitePayment.actual_integral G u hd)
    (WideAnchor228PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+12+0+2≤18) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 12 0 (((17/9) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((17/9)) (1/268435456) 128 target
    WideAnchor228Origin.payment WideAnchor228FinitePayment.payment WideAnchor228PositiveTail.payment 12 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor228Origin.actual_integral_swapped G u hN)
    (WideAnchor228FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor228PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor228OriginalAnchor
