/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor504Origin
import Proofs.RadenkovicGutmanWideAnchor504FinitePayment
import Proofs.RadenkovicGutmanWideAnchor504PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor504OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (28665496405055937255751154157731/393062208820009069919698461753344)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[504]?=some (⟨52,4,34,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor504Origin.payment+WideAnchor504FinitePayment.payment+WideAnchor504PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+34+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 34 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor504Origin.payment WideAnchor504FinitePayment.payment WideAnchor504PositiveTail.payment 4 34
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor504Origin.actual_integral G u hN)
    (WideAnchor504FinitePayment.actual_integral G u hd)
    (WideAnchor504PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+34+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 34 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor504Origin.payment WideAnchor504FinitePayment.payment WideAnchor504PositiveTail.payment 34 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor504Origin.actual_integral_swapped G u hN)
    (WideAnchor504FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor504PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor504OriginalAnchor
