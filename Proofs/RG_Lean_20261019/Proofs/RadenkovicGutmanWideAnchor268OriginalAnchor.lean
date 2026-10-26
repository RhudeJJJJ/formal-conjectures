/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor268Origin
import Proofs.RadenkovicGutmanWideAnchor268FinitePayment
import Proofs.RadenkovicGutmanWideAnchor268PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor268OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3107649274584561213395673949102121/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[268]?=some (⟨52,0,44,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor268Origin.payment+WideAnchor268FinitePayment.payment+WideAnchor268PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+44+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 44 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor268Origin.payment WideAnchor268FinitePayment.payment WideAnchor268PositiveTail.payment 0 44
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor268Origin.actual_integral G u hN)
    (WideAnchor268FinitePayment.actual_integral G u hd)
    (WideAnchor268PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+44+0+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 44 0 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor268Origin.payment WideAnchor268FinitePayment.payment WideAnchor268PositiveTail.payment 44 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor268Origin.actual_integral_swapped G u hN)
    (WideAnchor268FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor268PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor268OriginalAnchor
