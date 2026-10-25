/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor250Origin
import Proofs.RadenkovicGutmanWideAnchor250FinitePayment
import Proofs.RadenkovicGutmanWideAnchor250PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor250OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3522576931684644962946952327729/393062208820009069919698461753344)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[250]?=some (⟨16,0,2,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor250Origin.payment+WideAnchor250FinitePayment.payment+WideAnchor250PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+2+2≤16) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 2 (((15/8) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((15/8)) (1/268435456) 128 target
    WideAnchor250Origin.payment WideAnchor250FinitePayment.payment WideAnchor250PositiveTail.payment 0 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor250Origin.actual_integral G u hN)
    (WideAnchor250FinitePayment.actual_integral G u hd)
    (WideAnchor250PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+0+2≤16) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 0 (((15/8) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((15/8)) (1/268435456) 128 target
    WideAnchor250Origin.payment WideAnchor250FinitePayment.payment WideAnchor250PositiveTail.payment 2 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor250Origin.actual_integral_swapped G u hN)
    (WideAnchor250FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor250PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor250OriginalAnchor
