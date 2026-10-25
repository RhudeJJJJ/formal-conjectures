/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor498Origin
import Proofs.RadenkovicGutmanWideAnchor498FinitePayment
import Proofs.RadenkovicGutmanWideAnchor498PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor498OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2245162570487047452111355612733953/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[498]?=some (⟨52,4,28,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor498Origin.payment+WideAnchor498FinitePayment.payment+WideAnchor498PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+28+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 28 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor498Origin.payment WideAnchor498FinitePayment.payment WideAnchor498PositiveTail.payment 4 28
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor498Origin.actual_integral G u hN)
    (WideAnchor498FinitePayment.actual_integral G u hd)
    (WideAnchor498PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+28+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 28 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor498Origin.payment WideAnchor498FinitePayment.payment WideAnchor498PositiveTail.payment 28 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor498Origin.actual_integral_swapped G u hN)
    (WideAnchor498FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor498PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor498OriginalAnchor
