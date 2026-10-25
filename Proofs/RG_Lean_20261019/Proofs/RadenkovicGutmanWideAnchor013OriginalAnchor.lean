/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor013Origin
import Proofs.RadenkovicGutmanWideAnchor013FinitePayment
import Proofs.RadenkovicGutmanWideAnchor013PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor013OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3568422536320552398661310640115521/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[13]?=some (⟨52,9,22,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor013Origin.payment+WideAnchor013FinitePayment.payment+WideAnchor013PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+22+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 22 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor013Origin.payment WideAnchor013FinitePayment.payment WideAnchor013PositiveTail.payment 9 22
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor013Origin.actual_integral G u hN)
    (WideAnchor013FinitePayment.actual_integral G u hd)
    (WideAnchor013PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+22+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 22 9 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor013Origin.payment WideAnchor013FinitePayment.payment WideAnchor013PositiveTail.payment 22 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor013Origin.actual_integral_swapped G u hN)
    (WideAnchor013FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor013PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor013OriginalAnchor
