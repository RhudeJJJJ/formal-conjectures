/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor512Origin
import Proofs.RadenkovicGutmanWideAnchor512FinitePayment
import Proofs.RadenkovicGutmanWideAnchor512PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor512OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2531085248614890957107766702778529/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[512]?=some (⟨52,4,42,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor512Origin.payment+WideAnchor512FinitePayment.payment+WideAnchor512PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+42+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 42 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor512Origin.payment WideAnchor512FinitePayment.payment WideAnchor512PositiveTail.payment 4 42
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor512Origin.actual_integral G u hN)
    (WideAnchor512FinitePayment.actual_integral G u hd)
    (WideAnchor512PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+42+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 42 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor512Origin.payment WideAnchor512FinitePayment.payment WideAnchor512PositiveTail.payment 42 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor512Origin.actual_integral_swapped G u hN)
    (WideAnchor512FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor512PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor512OriginalAnchor
