/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor394Origin
import Proofs.RadenkovicGutmanWideAnchor394FinitePayment
import Proofs.RadenkovicGutmanWideAnchor394PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor394OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (348464370949270112737219853703193/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[394]?=some (⟨23,2,2,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor394Origin.payment+WideAnchor394FinitePayment.payment+WideAnchor394PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+2+2≤23) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 2 (((44/23) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((44/23)) (1/268435456) 128 target
    WideAnchor394Origin.payment WideAnchor394FinitePayment.payment WideAnchor394PositiveTail.payment 2 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor394Origin.actual_integral G u hN)
    (WideAnchor394FinitePayment.actual_integral G u hd)
    (WideAnchor394PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+2+2≤23) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 2 (((44/23) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((44/23)) (1/268435456) 128 target
    WideAnchor394Origin.payment WideAnchor394FinitePayment.payment WideAnchor394PositiveTail.payment 2 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor394Origin.actual_integral_swapped G u hN)
    (WideAnchor394FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor394PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor394OriginalAnchor
