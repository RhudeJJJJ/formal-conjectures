/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor269Origin
import Proofs.RadenkovicGutmanWideAnchor269FinitePayment
import Proofs.RadenkovicGutmanWideAnchor269PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor269OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3082094419488378399706421482957609/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[269]?=some (⟨52,0,45,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor269Origin.payment+WideAnchor269FinitePayment.payment+WideAnchor269PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+45+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 45 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor269Origin.payment WideAnchor269FinitePayment.payment WideAnchor269PositiveTail.payment 0 45
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor269Origin.actual_integral G u hN)
    (WideAnchor269FinitePayment.actual_integral G u hd)
    (WideAnchor269PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+45+0+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 45 0 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor269Origin.payment WideAnchor269FinitePayment.payment WideAnchor269PositiveTail.payment 45 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor269Origin.actual_integral_swapped G u hN)
    (WideAnchor269FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor269PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor269OriginalAnchor
