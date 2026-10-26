/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor432Origin
import Proofs.RadenkovicGutmanWideAnchor432FinitePayment
import Proofs.RadenkovicGutmanWideAnchor432PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor432OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (613460848874501732008391308823681/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[432]?=some (⟨17,2,8,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor432Origin.payment+WideAnchor432FinitePayment.payment+WideAnchor432PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+8+2≤17) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 8 (((32/17) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((32/17)) (1/268435456) 128 target
    WideAnchor432Origin.payment WideAnchor432FinitePayment.payment WideAnchor432PositiveTail.payment 2 8
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor432Origin.actual_integral G u hN)
    (WideAnchor432FinitePayment.actual_integral G u hd)
    (WideAnchor432PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+8+2+2≤17) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 8 2 (((32/17) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((32/17)) (1/268435456) 128 target
    WideAnchor432Origin.payment WideAnchor432FinitePayment.payment WideAnchor432PositiveTail.payment 8 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor432Origin.actual_integral_swapped G u hN)
    (WideAnchor432FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor432PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor432OriginalAnchor
