/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor249Origin
import Proofs.RadenkovicGutmanWideAnchor249FinitePayment
import Proofs.RadenkovicGutmanWideAnchor249PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor249OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (521481508135583741374308327204037/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[249]?=some (⟨19,0,2,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor249Origin.payment+WideAnchor249FinitePayment.payment+WideAnchor249PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+2+2≤19) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 2 (((36/19) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((36/19)) (1/268435456) 128 target
    WideAnchor249Origin.payment WideAnchor249FinitePayment.payment WideAnchor249PositiveTail.payment 0 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor249Origin.actual_integral G u hN)
    (WideAnchor249FinitePayment.actual_integral G u hd)
    (WideAnchor249PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+0+2≤19) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 0 (((36/19) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((36/19)) (1/268435456) 128 target
    WideAnchor249Origin.payment WideAnchor249FinitePayment.payment WideAnchor249PositiveTail.payment 2 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor249Origin.actual_integral_swapped G u hN)
    (WideAnchor249FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor249PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor249OriginalAnchor
