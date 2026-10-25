/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor020Origin
import Proofs.RadenkovicGutmanWideAnchor020FinitePayment
import Proofs.RadenkovicGutmanWideAnchor020PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor020OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3828769714491656906437082190665721/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[20]?=some (⟨52,9,29,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor020Origin.payment+WideAnchor020FinitePayment.payment+WideAnchor020PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+29+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 29 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor020Origin.payment WideAnchor020FinitePayment.payment WideAnchor020PositiveTail.payment 9 29
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor020Origin.actual_integral G u hN)
    (WideAnchor020FinitePayment.actual_integral G u hd)
    (WideAnchor020PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+29+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 29 9 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor020Origin.payment WideAnchor020FinitePayment.payment WideAnchor020PositiveTail.payment 29 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor020Origin.actual_integral_swapped G u hN)
    (WideAnchor020FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor020PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor020OriginalAnchor
