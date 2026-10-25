/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor374Origin
import Proofs.RadenkovicGutmanWideAnchor374FinitePayment
import Proofs.RadenkovicGutmanWideAnchor374PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor374OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1264860528665392311006893927233021/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[374]?=some (⟨22,2,12,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor374Origin.payment+WideAnchor374FinitePayment.payment+WideAnchor374PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+12+2≤22) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 12 (((21/11) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((21/11)) (1/268435456) 128 target
    WideAnchor374Origin.payment WideAnchor374FinitePayment.payment WideAnchor374PositiveTail.payment 2 12
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor374Origin.actual_integral G u hN)
    (WideAnchor374FinitePayment.actual_integral G u hd)
    (WideAnchor374PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+12+2+2≤22) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 12 2 (((21/11) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((21/11)) (1/268435456) 128 target
    WideAnchor374Origin.payment WideAnchor374FinitePayment.payment WideAnchor374PositiveTail.payment 12 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor374Origin.actual_integral_swapped G u hN)
    (WideAnchor374FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor374PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor374OriginalAnchor
