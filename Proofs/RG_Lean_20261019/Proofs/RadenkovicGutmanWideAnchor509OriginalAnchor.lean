/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor509Origin
import Proofs.RadenkovicGutmanWideAnchor509FinitePayment
import Proofs.RadenkovicGutmanWideAnchor509PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor509OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (70687697389978470721025488399261/881734144109750075765810062852096)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[509]?=some (⟨52,4,39,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor509Origin.payment+WideAnchor509FinitePayment.payment+WideAnchor509PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+39+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 39 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor509Origin.payment WideAnchor509FinitePayment.payment WideAnchor509PositiveTail.payment 4 39
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor509Origin.actual_integral G u hN)
    (WideAnchor509FinitePayment.actual_integral G u hd)
    (WideAnchor509PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+39+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 39 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor509Origin.payment WideAnchor509FinitePayment.payment WideAnchor509PositiveTail.payment 39 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor509Origin.actual_integral_swapped G u hN)
    (WideAnchor509FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor509PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor509OriginalAnchor
