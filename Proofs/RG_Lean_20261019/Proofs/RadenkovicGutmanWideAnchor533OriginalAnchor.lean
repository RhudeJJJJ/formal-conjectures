/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor533Origin
import Proofs.RadenkovicGutmanWideAnchor533FinitePayment
import Proofs.RadenkovicGutmanWideAnchor533PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor533OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (4022611780513879940044239241509081/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[533]?=some (⟨52,5,11,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor533Origin.payment+WideAnchor533FinitePayment.payment+WideAnchor533PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+5+11+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 5 11 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor533Origin.payment WideAnchor533FinitePayment.payment WideAnchor533PositiveTail.payment 5 11
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor533Origin.actual_integral G u hN)
    (WideAnchor533FinitePayment.actual_integral G u hd)
    (WideAnchor533PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+11+5+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 11 5 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor533Origin.payment WideAnchor533FinitePayment.payment WideAnchor533PositiveTail.payment 11 5
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor533Origin.actual_integral_swapped G u hN)
    (WideAnchor533FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor533PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor533OriginalAnchor
