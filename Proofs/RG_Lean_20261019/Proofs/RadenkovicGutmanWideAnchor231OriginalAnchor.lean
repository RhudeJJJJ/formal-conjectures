/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor231Origin
import Proofs.RadenkovicGutmanWideAnchor231FinitePayment
import Proofs.RadenkovicGutmanWideAnchor231PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor231OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2101198076087901640492484823363361/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[231]?=some (⟨18,0,14,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor231Origin.payment+WideAnchor231FinitePayment.payment+WideAnchor231PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+14+2≤18) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 14 (((17/9) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((17/9)) (1/268435456) 128 target
    WideAnchor231Origin.payment WideAnchor231FinitePayment.payment WideAnchor231PositiveTail.payment 0 14
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor231Origin.actual_integral G u hN)
    (WideAnchor231FinitePayment.actual_integral G u hd)
    (WideAnchor231PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+14+0+2≤18) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 14 0 (((17/9) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((17/9)) (1/268435456) 128 target
    WideAnchor231Origin.payment WideAnchor231FinitePayment.payment WideAnchor231PositiveTail.payment 14 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor231Origin.actual_integral_swapped G u hN)
    (WideAnchor231FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor231PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor231OriginalAnchor
