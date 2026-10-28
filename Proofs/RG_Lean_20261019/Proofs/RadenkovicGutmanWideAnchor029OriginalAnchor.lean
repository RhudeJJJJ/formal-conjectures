/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor029Origin
import Proofs.RadenkovicGutmanWideAnchor029FinitePayment
import Proofs.RadenkovicGutmanWideAnchor029PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor029OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3675063162842515354431878914926785/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[29]?=some (⟨52,9,38,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor029Origin.payment+WideAnchor029FinitePayment.payment+WideAnchor029PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+38+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 38 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor029Origin.payment WideAnchor029FinitePayment.payment WideAnchor029PositiveTail.payment 9 38
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor029Origin.actual_integral G u hN)
    (WideAnchor029FinitePayment.actual_integral G u hd)
    (WideAnchor029PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+38+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 38 9 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor029Origin.payment WideAnchor029FinitePayment.payment WideAnchor029PositiveTail.payment 38 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor029Origin.actual_integral_swapped G u hN)
    (WideAnchor029FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor029PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor029OriginalAnchor
