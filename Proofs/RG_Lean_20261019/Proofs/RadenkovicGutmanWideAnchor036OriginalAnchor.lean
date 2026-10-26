/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor036Origin
import Proofs.RadenkovicGutmanWideAnchor036FinitePayment
import Proofs.RadenkovicGutmanWideAnchor036PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor036OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3185305711182910612982048810218897/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[36]?=some (⟨52,10,15,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor036Origin.payment+WideAnchor036FinitePayment.payment+WideAnchor036PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+15+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 15 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor036Origin.payment WideAnchor036FinitePayment.payment WideAnchor036PositiveTail.payment 10 15
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor036Origin.actual_integral G u hN)
    (WideAnchor036FinitePayment.actual_integral G u hd)
    (WideAnchor036PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+15+10+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 15 10 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor036Origin.payment WideAnchor036FinitePayment.payment WideAnchor036PositiveTail.payment 15 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor036Origin.actual_integral_swapped G u hN)
    (WideAnchor036FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor036PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor036OriginalAnchor
