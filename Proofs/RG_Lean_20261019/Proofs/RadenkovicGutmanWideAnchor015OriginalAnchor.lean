/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor015Origin
import Proofs.RadenkovicGutmanWideAnchor015FinitePayment
import Proofs.RadenkovicGutmanWideAnchor015PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor015OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3584027086044232697897699728090889/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[15]?=some (⟨52,9,24,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor015Origin.payment+WideAnchor015FinitePayment.payment+WideAnchor015PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+24+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 24 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor015Origin.payment WideAnchor015FinitePayment.payment WideAnchor015PositiveTail.payment 9 24
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor015Origin.actual_integral G u hN)
    (WideAnchor015FinitePayment.actual_integral G u hd)
    (WideAnchor015PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+24+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 24 9 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor015Origin.payment WideAnchor015FinitePayment.payment WideAnchor015PositiveTail.payment 24 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor015Origin.actual_integral_swapped G u hN)
    (WideAnchor015FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor015PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor015OriginalAnchor
