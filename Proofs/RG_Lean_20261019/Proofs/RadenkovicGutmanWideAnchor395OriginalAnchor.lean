/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor395Origin
import Proofs.RadenkovicGutmanWideAnchor395FinitePayment
import Proofs.RadenkovicGutmanWideAnchor395PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor395OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (179118007152360289405150163981561/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[395]?=some (⟨20,2,2,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor395Origin.payment+WideAnchor395FinitePayment.payment+WideAnchor395PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+2+2≤20) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 2 (((19/10) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((19/10)) (1/268435456) 128 target
    WideAnchor395Origin.payment WideAnchor395FinitePayment.payment WideAnchor395PositiveTail.payment 2 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor395Origin.actual_integral G u hN)
    (WideAnchor395FinitePayment.actual_integral G u hd)
    (WideAnchor395PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+2+2≤20) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 2 (((19/10) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((19/10)) (1/268435456) 128 target
    WideAnchor395Origin.payment WideAnchor395FinitePayment.payment WideAnchor395PositiveTail.payment 2 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor395Origin.actual_integral_swapped G u hN)
    (WideAnchor395FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor395PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor395OriginalAnchor
