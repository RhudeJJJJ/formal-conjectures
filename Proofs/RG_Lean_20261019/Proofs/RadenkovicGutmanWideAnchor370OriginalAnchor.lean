/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor370Origin
import Proofs.RadenkovicGutmanWideAnchor370FinitePayment
import Proofs.RadenkovicGutmanWideAnchor370PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor370OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (1069762038478801678540222357790645/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[370]?=some (⟨22,2,10,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor370Origin.payment+WideAnchor370FinitePayment.payment+WideAnchor370PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+10+2≤22) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 10 (((21/11) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((21/11)) (1/268435456) 128 target
    WideAnchor370Origin.payment WideAnchor370FinitePayment.payment WideAnchor370PositiveTail.payment 2 10
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor370Origin.actual_integral G u hN)
    (WideAnchor370FinitePayment.actual_integral G u hd)
    (WideAnchor370PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+10+2+2≤22) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 10 2 (((21/11) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((21/11)) (1/268435456) 128 target
    WideAnchor370Origin.payment WideAnchor370FinitePayment.payment WideAnchor370PositiveTail.payment 10 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor370Origin.actual_integral_swapped G u hN)
    (WideAnchor370FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor370PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor370OriginalAnchor
