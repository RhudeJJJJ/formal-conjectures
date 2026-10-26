/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor521Origin
import Proofs.RadenkovicGutmanWideAnchor521FinitePayment
import Proofs.RadenkovicGutmanWideAnchor521PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor521OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1386733357702108312200317530534697/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[521]?=some (⟨52,4,6,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor521Origin.payment+WideAnchor521FinitePayment.payment+WideAnchor521PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+6+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 6 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor521Origin.payment WideAnchor521FinitePayment.payment WideAnchor521PositiveTail.payment 4 6
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor521Origin.actual_integral G u hN)
    (WideAnchor521FinitePayment.actual_integral G u hd)
    (WideAnchor521PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+6+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 6 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor521Origin.payment WideAnchor521FinitePayment.payment WideAnchor521PositiveTail.payment 6 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor521Origin.actual_integral_swapped G u hN)
    (WideAnchor521FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor521PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor521OriginalAnchor
