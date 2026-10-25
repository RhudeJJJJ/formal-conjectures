/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor497Origin
import Proofs.RadenkovicGutmanWideAnchor497FinitePayment
import Proofs.RadenkovicGutmanWideAnchor497PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor497OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2757394245957619687488077047189729/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[497]?=some (⟨52,4,27,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor497Origin.payment+WideAnchor497FinitePayment.payment+WideAnchor497PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+27+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 27 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor497Origin.payment WideAnchor497FinitePayment.payment WideAnchor497PositiveTail.payment 4 27
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor497Origin.actual_integral G u hN)
    (WideAnchor497FinitePayment.actual_integral G u hd)
    (WideAnchor497PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+27+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 27 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor497Origin.payment WideAnchor497FinitePayment.payment WideAnchor497PositiveTail.payment 27 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor497Origin.actual_integral_swapped G u hN)
    (WideAnchor497FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor497PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor497OriginalAnchor
