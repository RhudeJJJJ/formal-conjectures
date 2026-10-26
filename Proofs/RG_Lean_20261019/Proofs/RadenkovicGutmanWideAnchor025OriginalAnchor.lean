/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor025Origin
import Proofs.RadenkovicGutmanWideAnchor025FinitePayment
import Proofs.RadenkovicGutmanWideAnchor025PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor025OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (98688449284164004174277968677309/881734144109750075765810062852096)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[25]?=some (⟨52,9,34,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor025Origin.payment+WideAnchor025FinitePayment.payment+WideAnchor025PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+34+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 34 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor025Origin.payment WideAnchor025FinitePayment.payment WideAnchor025PositiveTail.payment 9 34
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor025Origin.actual_integral G u hN)
    (WideAnchor025FinitePayment.actual_integral G u hd)
    (WideAnchor025PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+34+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 34 9 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor025Origin.payment WideAnchor025FinitePayment.payment WideAnchor025PositiveTail.payment 34 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor025Origin.actual_integral_swapped G u hN)
    (WideAnchor025FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor025PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor025OriginalAnchor
