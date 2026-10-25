/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor496Origin
import Proofs.RadenkovicGutmanWideAnchor496FinitePayment
import Proofs.RadenkovicGutmanWideAnchor496PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor496OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2195423809777973189243369001296289/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[496]?=some (⟨52,4,26,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor496Origin.payment+WideAnchor496FinitePayment.payment+WideAnchor496PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+26+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 26 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor496Origin.payment WideAnchor496FinitePayment.payment WideAnchor496PositiveTail.payment 4 26
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor496Origin.actual_integral G u hN)
    (WideAnchor496FinitePayment.actual_integral G u hd)
    (WideAnchor496PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+26+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 26 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor496Origin.payment WideAnchor496FinitePayment.payment WideAnchor496PositiveTail.payment 26 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor496Origin.actual_integral_swapped G u hN)
    (WideAnchor496FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor496PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor496OriginalAnchor
