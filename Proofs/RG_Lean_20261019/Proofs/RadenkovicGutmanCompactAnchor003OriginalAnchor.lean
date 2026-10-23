/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCompactAnchor003Origin
import Proofs.RadenkovicGutmanCompactAnchor003FinitePayment
import Proofs.RadenkovicGutmanCompactAnchor003PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3468584578634352349460217430589169/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[3]?=some (⟨52,9,12,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤CompactAnchor003Origin.payment+CompactAnchor003FinitePayment.payment+CompactAnchor003PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+12+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 12 ((51/26 : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower (51/26) (1/268435456) 128 target
    CompactAnchor003Origin.payment CompactAnchor003FinitePayment.payment CompactAnchor003PositiveTail.payment 9 12
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (CompactAnchor003Origin.actual_integral G u hN)
    (CompactAnchor003FinitePayment.actual_integral G u hd)
    (CompactAnchor003PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+12+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 12 9 ((51/26 : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower (51/26) (1/268435456) 128 target
    CompactAnchor003Origin.payment CompactAnchor003FinitePayment.payment CompactAnchor003PositiveTail.payment 12 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (CompactAnchor003Origin.actual_integral_swapped G u hN)
    (CompactAnchor003FinitePayment.actual_integral_swapped G u hd)
    (CompactAnchor003PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.CompactAnchor003OriginalAnchor
