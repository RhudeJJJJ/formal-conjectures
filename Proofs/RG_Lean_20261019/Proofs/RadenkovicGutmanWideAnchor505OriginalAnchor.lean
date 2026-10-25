/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor505Origin
import Proofs.RadenkovicGutmanWideAnchor505FinitePayment
import Proofs.RadenkovicGutmanWideAnchor505PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor505OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2652020015189964708361485703256121/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[505]?=some (⟨52,4,35,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor505Origin.payment+WideAnchor505FinitePayment.payment+WideAnchor505PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+35+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 35 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor505Origin.payment WideAnchor505FinitePayment.payment WideAnchor505PositiveTail.payment 4 35
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor505Origin.actual_integral G u hN)
    (WideAnchor505FinitePayment.actual_integral G u hd)
    (WideAnchor505PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+35+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 35 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor505Origin.payment WideAnchor505FinitePayment.payment WideAnchor505PositiveTail.payment 35 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor505Origin.actual_integral_swapped G u hN)
    (WideAnchor505FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor505PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor505OriginalAnchor
