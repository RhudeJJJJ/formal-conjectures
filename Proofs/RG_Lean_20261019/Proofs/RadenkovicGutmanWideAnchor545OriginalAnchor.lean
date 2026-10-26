/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor545Origin
import Proofs.RadenkovicGutmanWideAnchor545FinitePayment
import Proofs.RadenkovicGutmanWideAnchor545PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor545OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3966608977065302404244351536274953/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[545]?=some (⟨52,5,23,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor545Origin.payment+WideAnchor545FinitePayment.payment+WideAnchor545PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+5+23+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 5 23 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor545Origin.payment WideAnchor545FinitePayment.payment WideAnchor545PositiveTail.payment 5 23
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor545Origin.actual_integral G u hN)
    (WideAnchor545FinitePayment.actual_integral G u hd)
    (WideAnchor545PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+23+5+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 23 5 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor545Origin.payment WideAnchor545FinitePayment.payment WideAnchor545PositiveTail.payment 23 5
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor545Origin.actual_integral_swapped G u hN)
    (WideAnchor545FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor545PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor545OriginalAnchor
