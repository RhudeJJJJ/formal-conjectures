/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor420Origin
import Proofs.RadenkovicGutmanWideAnchor420FinitePayment
import Proofs.RadenkovicGutmanWideAnchor420PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor420OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (111418223371182126187717044298441/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[420]?=some (⟨17,2,4,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor420Origin.payment+WideAnchor420FinitePayment.payment+WideAnchor420PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+4+2≤17) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 4 (((32/17) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((32/17)) (1/268435456) 128 target
    WideAnchor420Origin.payment WideAnchor420FinitePayment.payment WideAnchor420PositiveTail.payment 2 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor420Origin.actual_integral G u hN)
    (WideAnchor420FinitePayment.actual_integral G u hd)
    (WideAnchor420PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+2+2≤17) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 2 (((32/17) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((32/17)) (1/268435456) 128 target
    WideAnchor420Origin.payment WideAnchor420FinitePayment.payment WideAnchor420PositiveTail.payment 4 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor420Origin.actual_integral_swapped G u hN)
    (WideAnchor420FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor420PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor420OriginalAnchor
