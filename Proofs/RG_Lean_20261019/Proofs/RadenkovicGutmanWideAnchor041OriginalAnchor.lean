/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor041Origin
import Proofs.RadenkovicGutmanWideAnchor041FinitePayment
import Proofs.RadenkovicGutmanWideAnchor041PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor041OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2132104915064990540114247960981665/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[41]?=some (⟨52,10,20,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor041Origin.payment+WideAnchor041FinitePayment.payment+WideAnchor041PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+20+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 20 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor041Origin.payment WideAnchor041FinitePayment.payment WideAnchor041PositiveTail.payment 10 20
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor041Origin.actual_integral G u hN)
    (WideAnchor041FinitePayment.actual_integral G u hd)
    (WideAnchor041PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+20+10+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 20 10 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor041Origin.payment WideAnchor041FinitePayment.payment WideAnchor041PositiveTail.payment 20 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor041Origin.actual_integral_swapped G u hN)
    (WideAnchor041FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor041PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor041OriginalAnchor
