/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor371Origin
import Proofs.RadenkovicGutmanWideAnchor371FinitePayment
import Proofs.RadenkovicGutmanWideAnchor371PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor371OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (858220501208110390539501531334123/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[371]?=some (⟨16,2,10,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor371Origin.payment+WideAnchor371FinitePayment.payment+WideAnchor371PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+10+2≤16) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 10 (((15/8) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((15/8)) (1/268435456) 128 target
    WideAnchor371Origin.payment WideAnchor371FinitePayment.payment WideAnchor371PositiveTail.payment 2 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor371Origin.actual_integral G u hN)
    (WideAnchor371FinitePayment.actual_integral G u hd)
    (WideAnchor371PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+2+2≤16) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 2 (((15/8) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((15/8)) (1/268435456) 128 target
    WideAnchor371Origin.payment WideAnchor371FinitePayment.payment WideAnchor371PositiveTail.payment 10 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor371Origin.actual_integral_swapped G u hN)
    (WideAnchor371FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor371PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor371OriginalAnchor
