/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor279Origin
import Proofs.RadenkovicGutmanWideAnchor279FinitePayment
import Proofs.RadenkovicGutmanWideAnchor279PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor279OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1164740454000662066191853994627349/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[279]?=some (⟨21,0,6,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor279Origin.payment+WideAnchor279FinitePayment.payment+WideAnchor279PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+6+2≤21) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 6 (((40/21) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((40/21)) (1/268435456) 128 target
    WideAnchor279Origin.payment WideAnchor279FinitePayment.payment WideAnchor279PositiveTail.payment 0 6
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor279Origin.actual_integral G u hN)
    (WideAnchor279FinitePayment.actual_integral G u hd)
    (WideAnchor279PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+6+0+2≤21) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 6 0 (((40/21) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((40/21)) (1/268435456) 128 target
    WideAnchor279Origin.payment WideAnchor279FinitePayment.payment WideAnchor279PositiveTail.payment 6 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor279Origin.actual_integral_swapped G u hN)
    (WideAnchor279FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor279PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor279OriginalAnchor
