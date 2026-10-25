/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor251Origin
import Proofs.RadenkovicGutmanWideAnchor251FinitePayment
import Proofs.RadenkovicGutmanWideAnchor251PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor251OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (82447194237467593482428916939371/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[251]?=some (⟨14,0,2,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor251Origin.payment+WideAnchor251FinitePayment.payment+WideAnchor251PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+0+2+2≤14) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 0 2 (((13/7) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((13/7)) (1/268435456) 128 target
    WideAnchor251Origin.payment WideAnchor251FinitePayment.payment WideAnchor251PositiveTail.payment 0 2
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor251Origin.actual_integral G u hN)
    (WideAnchor251FinitePayment.actual_integral G u hd)
    (WideAnchor251PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+2+0+2≤14) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 2 0 (((13/7) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((13/7)) (1/268435456) 128 target
    WideAnchor251Origin.payment WideAnchor251FinitePayment.payment WideAnchor251PositiveTail.payment 2 0
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor251Origin.actual_integral_swapped G u hN)
    (WideAnchor251FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor251PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor251OriginalAnchor
