/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor427Origin
import Proofs.RadenkovicGutmanWideAnchor427FinitePayment
import Proofs.RadenkovicGutmanWideAnchor427PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor427OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (173820365133380736166631792553013/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[427]?=some (⟨15,2,6,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor427Origin.payment+WideAnchor427FinitePayment.payment+WideAnchor427PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+6+2≤15) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 6 (((28/15) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((28/15)) (1/268435456) 128 target
    WideAnchor427Origin.payment WideAnchor427FinitePayment.payment WideAnchor427PositiveTail.payment 2 6
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor427Origin.actual_integral G u hN)
    (WideAnchor427FinitePayment.actual_integral G u hd)
    (WideAnchor427PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+6+2+2≤15) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 6 2 (((28/15) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((28/15)) (1/268435456) 128 target
    WideAnchor427Origin.payment WideAnchor427FinitePayment.payment WideAnchor427PositiveTail.payment 6 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor427Origin.actual_integral_swapped G u hN)
    (WideAnchor427FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor427PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor427OriginalAnchor
