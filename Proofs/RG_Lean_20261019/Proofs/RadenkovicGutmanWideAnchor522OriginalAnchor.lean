/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor522Origin
import Proofs.RadenkovicGutmanWideAnchor522FinitePayment
import Proofs.RadenkovicGutmanWideAnchor522PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor522OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (791044281485057289673735643714509/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[522]?=some (⟨24,4,6,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor522Origin.payment+WideAnchor522FinitePayment.payment+WideAnchor522PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+6+2≤24) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 6 (((23/12) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((23/12)) (1/268435456) 128 target
    WideAnchor522Origin.payment WideAnchor522FinitePayment.payment WideAnchor522PositiveTail.payment 4 6
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor522Origin.actual_integral G u hN)
    (WideAnchor522FinitePayment.actual_integral G u hd)
    (WideAnchor522PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+6+4+2≤24) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 6 4 (((23/12) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((23/12)) (1/268435456) 128 target
    WideAnchor522Origin.payment WideAnchor522FinitePayment.payment WideAnchor522PositiveTail.payment 6 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor522Origin.actual_integral_swapped G u hN)
    (WideAnchor522FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor522PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor522OriginalAnchor
