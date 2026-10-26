/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor525Origin
import Proofs.RadenkovicGutmanWideAnchor525FinitePayment
import Proofs.RadenkovicGutmanWideAnchor525PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor525OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (133358403548992473688816224443965/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[525]?=some (⟨15,4,6,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor525Origin.payment+WideAnchor525FinitePayment.payment+WideAnchor525PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+6+2≤15) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 6 (((28/15) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((28/15)) (1/268435456) 128 target
    WideAnchor525Origin.payment WideAnchor525FinitePayment.payment WideAnchor525PositiveTail.payment 4 6
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor525Origin.actual_integral G u hN)
    (WideAnchor525FinitePayment.actual_integral G u hd)
    (WideAnchor525PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+6+4+2≤15) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 6 4 (((28/15) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((28/15)) (1/268435456) 128 target
    WideAnchor525Origin.payment WideAnchor525FinitePayment.payment WideAnchor525PositiveTail.payment 6 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor525Origin.actual_integral_swapped G u hN)
    (WideAnchor525FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor525PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor525OriginalAnchor
