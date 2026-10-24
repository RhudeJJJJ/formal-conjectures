/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor006Origin
import Proofs.RadenkovicGutmanSymbolicAnchor006FinitePayment
import Proofs.RadenkovicGutmanSymbolicAnchor006PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor006OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3879868802978334191604685791362961/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[6]?=some (⟨52,9,15,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤SymbolicAnchor006Origin.payment+SymbolicAnchor006FinitePayment.payment+SymbolicAnchor006PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+15+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 15 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    SymbolicAnchor006Origin.payment SymbolicAnchor006FinitePayment.payment SymbolicAnchor006PositiveTail.payment 9 15
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (SymbolicAnchor006Origin.actual_integral G u hN)
    (SymbolicAnchor006FinitePayment.actual_integral G u hd)
    (SymbolicAnchor006PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+15+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 15 9 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    SymbolicAnchor006Origin.payment SymbolicAnchor006FinitePayment.payment SymbolicAnchor006PositiveTail.payment 15 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (SymbolicAnchor006Origin.actual_integral_swapped G u hN)
    (SymbolicAnchor006FinitePayment.actual_integral_swapped G u hd)
    (SymbolicAnchor006PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.SymbolicAnchor006OriginalAnchor
