/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor519Origin
import Proofs.RadenkovicGutmanWideAnchor519FinitePayment
import Proofs.RadenkovicGutmanWideAnchor519PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor519OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (915054419736545274805206540489/393062208820009069919698461753344)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[519]?=some (⟨16,4,4,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor519Origin.payment+WideAnchor519FinitePayment.payment+WideAnchor519PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+4+2≤16) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 4 (((15/8) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((15/8)) (1/268435456) 128 target
    WideAnchor519Origin.payment WideAnchor519FinitePayment.payment WideAnchor519PositiveTail.payment 4 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor519Origin.actual_integral G u hN)
    (WideAnchor519FinitePayment.actual_integral G u hd)
    (WideAnchor519PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+4+2≤16) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 4 (((15/8) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((15/8)) (1/268435456) 128 target
    WideAnchor519Origin.payment WideAnchor519FinitePayment.payment WideAnchor519PositiveTail.payment 4 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor519Origin.actual_integral_swapped G u hN)
    (WideAnchor519FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor519PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor519OriginalAnchor
