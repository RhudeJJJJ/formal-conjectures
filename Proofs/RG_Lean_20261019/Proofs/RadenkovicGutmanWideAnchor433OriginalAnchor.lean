/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor433Origin
import Proofs.RadenkovicGutmanWideAnchor433FinitePayment
import Proofs.RadenkovicGutmanWideAnchor433PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor433OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (421523769207221983929066277800763/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[433]?=some (⟨14,2,8,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor433Origin.payment+WideAnchor433FinitePayment.payment+WideAnchor433PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+8+2≤14) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 8 (((13/7) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((13/7)) (1/268435456) 128 target
    WideAnchor433Origin.payment WideAnchor433FinitePayment.payment WideAnchor433PositiveTail.payment 2 8
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor433Origin.actual_integral G u hN)
    (WideAnchor433FinitePayment.actual_integral G u hd)
    (WideAnchor433PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+8+2+2≤14) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 8 2 (((13/7) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((13/7)) (1/268435456) 128 target
    WideAnchor433Origin.payment WideAnchor433FinitePayment.payment WideAnchor433PositiveTail.payment 8 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor433Origin.actual_integral_swapped G u hN)
    (WideAnchor433FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor433PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor433OriginalAnchor
