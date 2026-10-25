/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor225Origin
import Proofs.RadenkovicGutmanWideAnchor225FinitePayment
import Proofs.RadenkovicGutmanWideAnchor225PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor225OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1609457825895822180853853820579325/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[225]?=some (⟨19,0,10,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor225Origin.payment+WideAnchor225FinitePayment.payment+WideAnchor225PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+10+2≤19) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 10 (((36/19) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((36/19)) (1/268435456) 128 target
    WideAnchor225Origin.payment WideAnchor225FinitePayment.payment WideAnchor225PositiveTail.payment 0 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor225Origin.actual_integral G u hN)
    (WideAnchor225FinitePayment.actual_integral G u hd)
    (WideAnchor225PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+0+2≤19) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 0 (((36/19) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((36/19)) (1/268435456) 128 target
    WideAnchor225Origin.payment WideAnchor225FinitePayment.payment WideAnchor225PositiveTail.payment 10 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor225Origin.actual_integral_swapped G u hN)
    (WideAnchor225FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor225PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor225OriginalAnchor
