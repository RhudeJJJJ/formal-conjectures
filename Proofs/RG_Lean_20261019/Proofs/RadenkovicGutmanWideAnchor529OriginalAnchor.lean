/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor529Origin
import Proofs.RadenkovicGutmanWideAnchor529FinitePayment
import Proofs.RadenkovicGutmanWideAnchor529PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor529OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (901050077507243009569313455480985/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[529]?=some (⟨23,4,8,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor529Origin.payment+WideAnchor529FinitePayment.payment+WideAnchor529PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+8+2≤23) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 8 (((44/23) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((44/23)) (1/268435456) 128 target
    WideAnchor529Origin.payment WideAnchor529FinitePayment.payment WideAnchor529PositiveTail.payment 4 8
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor529Origin.actual_integral G u hN)
    (WideAnchor529FinitePayment.actual_integral G u hd)
    (WideAnchor529PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+8+4+2≤23) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 8 4 (((44/23) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((44/23)) (1/268435456) 128 target
    WideAnchor529Origin.payment WideAnchor529FinitePayment.payment WideAnchor529PositiveTail.payment 8 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor529Origin.actual_integral_swapped G u hN)
    (WideAnchor529FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor529PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor529OriginalAnchor
