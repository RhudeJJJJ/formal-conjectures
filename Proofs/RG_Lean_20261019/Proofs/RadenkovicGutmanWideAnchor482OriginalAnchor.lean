/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor482Origin
import Proofs.RadenkovicGutmanWideAnchor482FinitePayment
import Proofs.RadenkovicGutmanWideAnchor482PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor482OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1172628527627191913124585631913269/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[482]?=some (⟨21,4,12,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor482Origin.payment+WideAnchor482FinitePayment.payment+WideAnchor482PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+12+2≤21) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 12 (((40/21) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((40/21)) (1/268435456) 128 target
    WideAnchor482Origin.payment WideAnchor482FinitePayment.payment WideAnchor482PositiveTail.payment 4 12
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor482Origin.actual_integral G u hN)
    (WideAnchor482FinitePayment.actual_integral G u hd)
    (WideAnchor482PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+12+4+2≤21) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 12 4 (((40/21) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((40/21)) (1/268435456) 128 target
    WideAnchor482Origin.payment WideAnchor482FinitePayment.payment WideAnchor482PositiveTail.payment 12 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor482Origin.actual_integral_swapped G u hN)
    (WideAnchor482FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor482PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor482OriginalAnchor
