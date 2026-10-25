/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor248Origin
import Proofs.RadenkovicGutmanWideAnchor248FinitePayment
import Proofs.RadenkovicGutmanWideAnchor248PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor248OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (809972874235887460196139347310993/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[248]?=some (⟨25,0,2,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor248Origin.payment+WideAnchor248FinitePayment.payment+WideAnchor248PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+2+2≤25) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 2 (((48/25) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((48/25)) (1/268435456) 128 target
    WideAnchor248Origin.payment WideAnchor248FinitePayment.payment WideAnchor248PositiveTail.payment 0 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor248Origin.actual_integral G u hN)
    (WideAnchor248FinitePayment.actual_integral G u hd)
    (WideAnchor248PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+0+2≤25) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 0 (((48/25) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((48/25)) (1/268435456) 128 target
    WideAnchor248Origin.payment WideAnchor248FinitePayment.payment WideAnchor248PositiveTail.payment 2 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor248Origin.actual_integral_swapped G u hN)
    (WideAnchor248FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor248PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor248OriginalAnchor
