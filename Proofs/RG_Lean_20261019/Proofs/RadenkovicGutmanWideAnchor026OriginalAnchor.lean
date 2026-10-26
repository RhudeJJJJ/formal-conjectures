/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor026Origin
import Proofs.RadenkovicGutmanWideAnchor026FinitePayment
import Proofs.RadenkovicGutmanWideAnchor026PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor026OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3824245660436955096303396208705897/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[26]?=some (⟨52,9,35,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor026Origin.payment+WideAnchor026FinitePayment.payment+WideAnchor026PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+35+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 35 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor026Origin.payment WideAnchor026FinitePayment.payment WideAnchor026PositiveTail.payment 9 35
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor026Origin.actual_integral G u hN)
    (WideAnchor026FinitePayment.actual_integral G u hd)
    (WideAnchor026PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+35+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 35 9 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor026Origin.payment WideAnchor026FinitePayment.payment WideAnchor026PositiveTail.payment 35 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor026Origin.actual_integral_swapped G u hN)
    (WideAnchor026FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor026PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor026OriginalAnchor
