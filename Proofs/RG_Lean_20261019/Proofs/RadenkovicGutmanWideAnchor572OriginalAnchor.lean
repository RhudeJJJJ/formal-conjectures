/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor572Origin
import Proofs.RadenkovicGutmanWideAnchor572FinitePayment
import Proofs.RadenkovicGutmanWideAnchor572PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor572OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1044271729361196158488811370117333/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[572]?=some (⟨22,6,10,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor572Origin.payment+WideAnchor572FinitePayment.payment+WideAnchor572PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+6+10+2≤22) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 6 10 (((21/11) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((21/11)) (1/268435456) 128 target
    WideAnchor572Origin.payment WideAnchor572FinitePayment.payment WideAnchor572PositiveTail.payment 6 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor572Origin.actual_integral G u hN)
    (WideAnchor572FinitePayment.actual_integral G u hd)
    (WideAnchor572PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+6+2≤22) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 6 (((21/11) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((21/11)) (1/268435456) 128 target
    WideAnchor572Origin.payment WideAnchor572FinitePayment.payment WideAnchor572PositiveTail.payment 10 6
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor572Origin.actual_integral_swapped G u hN)
    (WideAnchor572FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor572PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor572OriginalAnchor
