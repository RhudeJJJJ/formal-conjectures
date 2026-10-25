/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor280Origin
import Proofs.RadenkovicGutmanWideAnchor280FinitePayment
import Proofs.RadenkovicGutmanWideAnchor280PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor280OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (834641119631651055618585432766933/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[280]?=some (⟨15,0,6,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor280Origin.payment+WideAnchor280FinitePayment.payment+WideAnchor280PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+6+2≤15) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 6 (((28/15) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((28/15)) (1/268435456) 128 target
    WideAnchor280Origin.payment WideAnchor280FinitePayment.payment WideAnchor280PositiveTail.payment 0 6
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor280Origin.actual_integral G u hN)
    (WideAnchor280FinitePayment.actual_integral G u hd)
    (WideAnchor280PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+6+0+2≤15) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 6 0 (((28/15) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((28/15)) (1/268435456) 128 target
    WideAnchor280Origin.payment WideAnchor280FinitePayment.payment WideAnchor280PositiveTail.payment 6 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor280Origin.actual_integral_swapped G u hN)
    (WideAnchor280FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor280PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor280OriginalAnchor
