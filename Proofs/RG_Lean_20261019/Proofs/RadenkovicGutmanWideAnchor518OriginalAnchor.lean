/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor518Origin
import Proofs.RadenkovicGutmanWideAnchor518FinitePayment
import Proofs.RadenkovicGutmanWideAnchor518PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor518OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (177598281244928640521953800214929/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[518]?=some (⟨17,4,4,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor518Origin.payment+WideAnchor518FinitePayment.payment+WideAnchor518PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+4+2≤17) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 4 (((32/17) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((32/17)) (1/268435456) 128 target
    WideAnchor518Origin.payment WideAnchor518FinitePayment.payment WideAnchor518PositiveTail.payment 4 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor518Origin.actual_integral G u hN)
    (WideAnchor518FinitePayment.actual_integral G u hd)
    (WideAnchor518PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+4+2≤17) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 4 (((32/17) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((32/17)) (1/268435456) 128 target
    WideAnchor518Origin.payment WideAnchor518FinitePayment.payment WideAnchor518PositiveTail.payment 4 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor518Origin.actual_integral_swapped G u hN)
    (WideAnchor518FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor518PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor518OriginalAnchor
