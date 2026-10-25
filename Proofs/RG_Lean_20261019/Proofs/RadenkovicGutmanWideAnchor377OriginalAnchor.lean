/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor377Origin
import Proofs.RadenkovicGutmanWideAnchor377FinitePayment
import Proofs.RadenkovicGutmanWideAnchor377PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor377OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1445510543010401268907019528834813/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[377]?=some (⟨21,2,14,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor377Origin.payment+WideAnchor377FinitePayment.payment+WideAnchor377PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+14+2≤21) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 14 (((40/21) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((40/21)) (1/268435456) 128 target
    WideAnchor377Origin.payment WideAnchor377FinitePayment.payment WideAnchor377PositiveTail.payment 2 14
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor377Origin.actual_integral G u hN)
    (WideAnchor377FinitePayment.actual_integral G u hd)
    (WideAnchor377PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+14+2+2≤21) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 14 2 (((40/21) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((40/21)) (1/268435456) 128 target
    WideAnchor377Origin.payment WideAnchor377FinitePayment.payment WideAnchor377PositiveTail.payment 14 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor377Origin.actual_integral_swapped G u hN)
    (WideAnchor377FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor377PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor377OriginalAnchor
