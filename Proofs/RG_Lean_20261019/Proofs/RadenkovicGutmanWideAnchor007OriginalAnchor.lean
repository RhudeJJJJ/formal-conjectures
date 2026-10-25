/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor007Origin
import Proofs.RadenkovicGutmanWideAnchor007FinitePayment
import Proofs.RadenkovicGutmanWideAnchor007PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor007OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3514307512232708957510494425500545/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[7]?=some (⟨52,9,16,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor007Origin.payment+WideAnchor007FinitePayment.payment+WideAnchor007PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+16+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 16 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor007Origin.payment WideAnchor007FinitePayment.payment WideAnchor007PositiveTail.payment 9 16
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor007Origin.actual_integral G u hN)
    (WideAnchor007FinitePayment.actual_integral G u hd)
    (WideAnchor007PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+16+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 16 9 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor007Origin.payment WideAnchor007FinitePayment.payment WideAnchor007PositiveTail.payment 16 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor007Origin.actual_integral_swapped G u hN)
    (WideAnchor007FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor007PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor007OriginalAnchor
