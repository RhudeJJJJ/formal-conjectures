/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor393Origin
import Proofs.RadenkovicGutmanWideAnchor393FinitePayment
import Proofs.RadenkovicGutmanWideAnchor393PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor393OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (578705136251680256455700956627277/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[393]?=some (⟨29,2,2,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor393Origin.payment+WideAnchor393FinitePayment.payment+WideAnchor393PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+2+2≤29) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 2 (((56/29) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((56/29)) (1/268435456) 128 target
    WideAnchor393Origin.payment WideAnchor393FinitePayment.payment WideAnchor393PositiveTail.payment 2 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor393Origin.actual_integral G u hN)
    (WideAnchor393FinitePayment.actual_integral G u hd)
    (WideAnchor393PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+2+2≤29) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 2 (((56/29) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((56/29)) (1/268435456) 128 target
    WideAnchor393Origin.payment WideAnchor393FinitePayment.payment WideAnchor393PositiveTail.payment 2 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor393Origin.actual_integral_swapped G u hN)
    (WideAnchor393FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor393PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor393OriginalAnchor
