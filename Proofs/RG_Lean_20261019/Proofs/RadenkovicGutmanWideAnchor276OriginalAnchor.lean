/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor276Origin
import Proofs.RadenkovicGutmanWideAnchor276FinitePayment
import Proofs.RadenkovicGutmanWideAnchor276PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor276OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (387083688802718400270273490156635/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[276]?=some (⟨14,0,4,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor276Origin.payment+WideAnchor276FinitePayment.payment+WideAnchor276PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+4+2≤14) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 4 (((13/7) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((13/7)) (1/268435456) 128 target
    WideAnchor276Origin.payment WideAnchor276FinitePayment.payment WideAnchor276PositiveTail.payment 0 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor276Origin.actual_integral G u hN)
    (WideAnchor276FinitePayment.actual_integral G u hd)
    (WideAnchor276PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+0+2≤14) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 0 (((13/7) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((13/7)) (1/268435456) 128 target
    WideAnchor276Origin.payment WideAnchor276FinitePayment.payment WideAnchor276PositiveTail.payment 4 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor276Origin.actual_integral_swapped G u hN)
    (WideAnchor276FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor276PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor276OriginalAnchor
