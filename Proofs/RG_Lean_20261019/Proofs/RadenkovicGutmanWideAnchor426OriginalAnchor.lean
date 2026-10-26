/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor426Origin
import Proofs.RadenkovicGutmanWideAnchor426FinitePayment
import Proofs.RadenkovicGutmanWideAnchor426PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor426OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (266556351869351005570176158087739/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[426]?=some (⟨16,2,6,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor426Origin.payment+WideAnchor426FinitePayment.payment+WideAnchor426PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+6+2≤16) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 6 (((15/8) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((15/8)) (1/268435456) 128 target
    WideAnchor426Origin.payment WideAnchor426FinitePayment.payment WideAnchor426PositiveTail.payment 2 6
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor426Origin.actual_integral G u hN)
    (WideAnchor426FinitePayment.actual_integral G u hd)
    (WideAnchor426PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+6+2+2≤16) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 6 2 (((15/8) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((15/8)) (1/268435456) 128 target
    WideAnchor426Origin.payment WideAnchor426FinitePayment.payment WideAnchor426PositiveTail.payment 6 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor426Origin.actual_integral_swapped G u hN)
    (WideAnchor426FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor426PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor426OriginalAnchor
