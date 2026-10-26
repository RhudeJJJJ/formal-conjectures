/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor528Origin
import Proofs.RadenkovicGutmanWideAnchor528FinitePayment
import Proofs.RadenkovicGutmanWideAnchor528PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor528OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1513305993892104549027302675358057/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[528]?=some (⟨52,4,8,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor528Origin.payment+WideAnchor528FinitePayment.payment+WideAnchor528PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+8+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 8 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor528Origin.payment WideAnchor528FinitePayment.payment WideAnchor528PositiveTail.payment 4 8
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor528Origin.actual_integral G u hN)
    (WideAnchor528FinitePayment.actual_integral G u hd)
    (WideAnchor528PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+8+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 8 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor528Origin.payment WideAnchor528FinitePayment.payment WideAnchor528PositiveTail.payment 8 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor528Origin.actual_integral_swapped G u hN)
    (WideAnchor528FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor528PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor528OriginalAnchor
