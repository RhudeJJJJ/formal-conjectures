/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor037Origin
import Proofs.RadenkovicGutmanWideAnchor037FinitePayment
import Proofs.RadenkovicGutmanWideAnchor037PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor037OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2027516889146047725829817934172393/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[37]?=some (⟨52,10,16,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor037Origin.payment+WideAnchor037FinitePayment.payment+WideAnchor037PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+16+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 16 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor037Origin.payment WideAnchor037FinitePayment.payment WideAnchor037PositiveTail.payment 10 16
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor037Origin.actual_integral G u hN)
    (WideAnchor037FinitePayment.actual_integral G u hd)
    (WideAnchor037PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+16+10+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 16 10 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor037Origin.payment WideAnchor037FinitePayment.payment WideAnchor037PositiveTail.payment 16 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor037Origin.actual_integral_swapped G u hN)
    (WideAnchor037FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor037PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor037OriginalAnchor
