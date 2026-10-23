/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCompactAnchor000Origin
import Proofs.RadenkovicGutmanCompactAnchor000FinitePayment
import Proofs.RadenkovicGutmanCompactAnchor000PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (3949369501170259056731373497378897/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[0]?=some (⟨52,9,9,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤CompactAnchor000Origin.payment+CompactAnchor000FinitePayment.payment+CompactAnchor000PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+9+9+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 9 9 ((51/26 : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower (51/26) (1/268435456) 128 target
    CompactAnchor000Origin.payment CompactAnchor000FinitePayment.payment CompactAnchor000PositiveTail.payment 9 9
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (CompactAnchor000Origin.actual_integral G u hN)
    (CompactAnchor000FinitePayment.actual_integral G u hd)
    (CompactAnchor000PositiveTail.actual_integral G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
end Gebendorfer.RadenkovicGutman.CompactAnchor000OriginalAnchor
