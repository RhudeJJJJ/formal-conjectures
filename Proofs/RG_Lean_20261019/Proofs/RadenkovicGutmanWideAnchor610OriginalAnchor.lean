/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor610Origin
import Proofs.RadenkovicGutmanWideAnchor610FinitePayment
import Proofs.RadenkovicGutmanWideAnchor610PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor610OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (24489377169192705482296737989369/881734144109750075765810062852096)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[610]?=some (⟨22,6,8,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor610Origin.payment+WideAnchor610FinitePayment.payment+WideAnchor610PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+6+8+2≤22) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 6 8 (((21/11) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((21/11)) (1/268435456) 128 target
    WideAnchor610Origin.payment WideAnchor610FinitePayment.payment WideAnchor610PositiveTail.payment 6 8
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor610Origin.actual_integral G u hN)
    (WideAnchor610FinitePayment.actual_integral G u hd)
    (WideAnchor610PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+8+6+2≤22) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 8 6 (((21/11) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((21/11)) (1/268435456) 128 target
    WideAnchor610Origin.payment WideAnchor610FinitePayment.payment WideAnchor610PositiveTail.payment 8 6
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor610Origin.actual_integral_swapped G u hN)
    (WideAnchor610FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor610PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor610OriginalAnchor
