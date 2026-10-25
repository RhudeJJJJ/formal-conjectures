/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor261Origin
import Proofs.RadenkovicGutmanWideAnchor261FinitePayment
import Proofs.RadenkovicGutmanWideAnchor261PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor261OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3004457365196724055128055578542801/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[261]?=some (⟨52,0,38,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor261Origin.payment+WideAnchor261FinitePayment.payment+WideAnchor261PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+38+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 38 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor261Origin.payment WideAnchor261FinitePayment.payment WideAnchor261PositiveTail.payment 0 38
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor261Origin.actual_integral G u hN)
    (WideAnchor261FinitePayment.actual_integral G u hd)
    (WideAnchor261PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+38+0+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 38 0 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor261Origin.payment WideAnchor261FinitePayment.payment WideAnchor261PositiveTail.payment 38 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor261Origin.actual_integral_swapped G u hN)
    (WideAnchor261FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor261PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor261OriginalAnchor
