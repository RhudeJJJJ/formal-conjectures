/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor417Origin
import Proofs.RadenkovicGutmanWideAnchor417FinitePayment
import Proofs.RadenkovicGutmanWideAnchor417PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor417OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (675277912038533252704267385695041/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[417]?=some (⟨27,2,4,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor417Origin.payment+WideAnchor417FinitePayment.payment+WideAnchor417PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+4+2≤27) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 4 (((52/27) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((52/27)) (1/268435456) 128 target
    WideAnchor417Origin.payment WideAnchor417FinitePayment.payment WideAnchor417PositiveTail.payment 2 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor417Origin.actual_integral G u hN)
    (WideAnchor417FinitePayment.actual_integral G u hd)
    (WideAnchor417PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+2+2≤27) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 2 (((52/27) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((52/27)) (1/268435456) 128 target
    WideAnchor417Origin.payment WideAnchor417FinitePayment.payment WideAnchor417PositiveTail.payment 4 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor417Origin.actual_integral_swapped G u hN)
    (WideAnchor417FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor417PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor417OriginalAnchor
