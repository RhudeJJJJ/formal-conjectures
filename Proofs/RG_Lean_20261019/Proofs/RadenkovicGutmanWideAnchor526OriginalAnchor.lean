/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor526Origin
import Proofs.RadenkovicGutmanWideAnchor526FinitePayment
import Proofs.RadenkovicGutmanWideAnchor526PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor526OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (10990500657013196902325632019531/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[526]?=some (⟨14,4,6,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor526Origin.payment+WideAnchor526FinitePayment.payment+WideAnchor526PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+6+2≤14) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 6 (((13/7) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((13/7)) (1/268435456) 128 target
    WideAnchor526Origin.payment WideAnchor526FinitePayment.payment WideAnchor526PositiveTail.payment 4 6
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor526Origin.actual_integral G u hN)
    (WideAnchor526FinitePayment.actual_integral G u hd)
    (WideAnchor526PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+6+4+2≤14) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 6 4 (((13/7) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((13/7)) (1/268435456) 128 target
    WideAnchor526Origin.payment WideAnchor526FinitePayment.payment WideAnchor526PositiveTail.payment 6 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor526Origin.actual_integral_swapped G u hN)
    (WideAnchor526FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor526PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor526OriginalAnchor
