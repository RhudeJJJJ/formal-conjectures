/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor031Origin
import Proofs.RadenkovicGutmanWideAnchor031FinitePayment
import Proofs.RadenkovicGutmanWideAnchor031PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor031OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1846242961327353873352431641334305/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[31]?=some (⟨52,10,10,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor031Origin.payment+WideAnchor031FinitePayment.payment+WideAnchor031PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+10+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 10 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor031Origin.payment WideAnchor031FinitePayment.payment WideAnchor031PositiveTail.payment 10 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor031Origin.actual_integral G u hN)
    (WideAnchor031FinitePayment.actual_integral G u hd)
    (WideAnchor031PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+10+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 10 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor031Origin.payment WideAnchor031FinitePayment.payment WideAnchor031PositiveTail.payment 10 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor031Origin.actual_integral_swapped G u hN)
    (WideAnchor031FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor031PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor031OriginalAnchor
