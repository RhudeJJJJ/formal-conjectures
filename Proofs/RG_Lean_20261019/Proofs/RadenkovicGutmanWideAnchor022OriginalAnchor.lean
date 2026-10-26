/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor022Origin
import Proofs.RadenkovicGutmanWideAnchor022FinitePayment
import Proofs.RadenkovicGutmanWideAnchor022PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor022OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3826591621821569498243874765005953/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[22]?=some (⟨52,9,31,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor022Origin.payment+WideAnchor022FinitePayment.payment+WideAnchor022PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+31+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 31 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor022Origin.payment WideAnchor022FinitePayment.payment WideAnchor022PositiveTail.payment 9 31
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor022Origin.actual_integral G u hN)
    (WideAnchor022FinitePayment.actual_integral G u hd)
    (WideAnchor022PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+31+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 31 9 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor022Origin.payment WideAnchor022FinitePayment.payment WideAnchor022PositiveTail.payment 31 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor022Origin.actual_integral_swapped G u hN)
    (WideAnchor022FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor022PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor022OriginalAnchor
