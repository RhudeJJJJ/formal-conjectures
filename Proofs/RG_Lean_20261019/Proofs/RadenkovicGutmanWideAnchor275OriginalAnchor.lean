/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor275Origin
import Proofs.RadenkovicGutmanWideAnchor275FinitePayment
import Proofs.RadenkovicGutmanWideAnchor275PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor275OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (651208424012322916329742388961537/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[275]?=some (⟨17,0,4,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor275Origin.payment+WideAnchor275FinitePayment.payment+WideAnchor275PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+4+2≤17) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 4 (((32/17) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((32/17)) (1/268435456) 128 target
    WideAnchor275Origin.payment WideAnchor275FinitePayment.payment WideAnchor275PositiveTail.payment 0 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor275Origin.actual_integral G u hN)
    (WideAnchor275FinitePayment.actual_integral G u hd)
    (WideAnchor275PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+0+2≤17) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 0 (((32/17) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((32/17)) (1/268435456) 128 target
    WideAnchor275Origin.payment WideAnchor275FinitePayment.payment WideAnchor275PositiveTail.payment 4 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor275Origin.actual_integral_swapped G u hN)
    (WideAnchor275FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor275PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor275OriginalAnchor
