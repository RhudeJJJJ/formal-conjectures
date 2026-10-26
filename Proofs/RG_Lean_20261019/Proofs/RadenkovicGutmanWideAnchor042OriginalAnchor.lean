/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor042Origin
import Proofs.RadenkovicGutmanWideAnchor042FinitePayment
import Proofs.RadenkovicGutmanWideAnchor042PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor042OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3017284545165972944440193870751153/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[42]?=some (⟨52,10,21,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor042Origin.payment+WideAnchor042FinitePayment.payment+WideAnchor042PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+21+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 21 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor042Origin.payment WideAnchor042FinitePayment.payment WideAnchor042PositiveTail.payment 10 21
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor042Origin.actual_integral G u hN)
    (WideAnchor042FinitePayment.actual_integral G u hd)
    (WideAnchor042PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+21+10+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 21 10 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor042Origin.payment WideAnchor042FinitePayment.payment WideAnchor042PositiveTail.payment 21 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor042Origin.actual_integral_swapped G u hN)
    (WideAnchor042FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor042PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor042OriginalAnchor
