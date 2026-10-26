/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor531Origin
import Proofs.RadenkovicGutmanWideAnchor531FinitePayment
import Proofs.RadenkovicGutmanWideAnchor531PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor531OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (4044686217008714236059834319737657/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[531]?=some (⟨52,5,9,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor531Origin.payment+WideAnchor531FinitePayment.payment+WideAnchor531PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+5+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 5 9 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor531Origin.payment WideAnchor531FinitePayment.payment WideAnchor531PositiveTail.payment 5 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor531Origin.actual_integral G u hN)
    (WideAnchor531FinitePayment.actual_integral G u hd)
    (WideAnchor531PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+5+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 5 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor531Origin.payment WideAnchor531FinitePayment.payment WideAnchor531PositiveTail.payment 9 5
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor531Origin.actual_integral_swapped G u hN)
    (WideAnchor531FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor531PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor531OriginalAnchor
