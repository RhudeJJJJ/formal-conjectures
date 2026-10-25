/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor260Origin
import Proofs.RadenkovicGutmanWideAnchor260FinitePayment
import Proofs.RadenkovicGutmanWideAnchor260PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor260OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3132639625585186609558167308672921/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[260]?=some (⟨52,0,37,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor260Origin.payment+WideAnchor260FinitePayment.payment+WideAnchor260PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+37+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 37 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor260Origin.payment WideAnchor260FinitePayment.payment WideAnchor260PositiveTail.payment 0 37
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor260Origin.actual_integral G u hN)
    (WideAnchor260FinitePayment.actual_integral G u hd)
    (WideAnchor260PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+37+0+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 37 0 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor260Origin.payment WideAnchor260FinitePayment.payment WideAnchor260PositiveTail.payment 37 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor260Origin.actual_integral_swapped G u hN)
    (WideAnchor260FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor260PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor260OriginalAnchor
