/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor038Origin
import Proofs.RadenkovicGutmanWideAnchor038FinitePayment
import Proofs.RadenkovicGutmanWideAnchor038PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor038OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3122035961317528809325397853641513/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[38]?=some (⟨52,10,17,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor038Origin.payment+WideAnchor038FinitePayment.payment+WideAnchor038PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+17+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 17 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor038Origin.payment WideAnchor038FinitePayment.payment WideAnchor038PositiveTail.payment 10 17
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor038Origin.actual_integral G u hN)
    (WideAnchor038FinitePayment.actual_integral G u hd)
    (WideAnchor038PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+17+10+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 17 10 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor038Origin.payment WideAnchor038FinitePayment.payment WideAnchor038PositiveTail.payment 17 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor038Origin.actual_integral_swapped G u hN)
    (WideAnchor038FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor038PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor038OriginalAnchor
