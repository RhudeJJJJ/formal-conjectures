/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor502Origin
import Proofs.RadenkovicGutmanWideAnchor502FinitePayment
import Proofs.RadenkovicGutmanWideAnchor502PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.WideAnchor502OriginalAnchor
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def target : ℚ := (2336785397436515460549690672276329/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[502]?=some (⟨52,4,32,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel
theorem budget_checked : target*(3927/1250)≤WideAnchor502Origin.payment+WideAnchor502FinitePayment.payment+WideAnchor502PositiveTail.payment := by decide +kernel
noncomputable section
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+4+32+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 4 32 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor502Origin.payment WideAnchor502FinitePayment.payment WideAnchor502PositiveTail.payment 4 32
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor502Origin.actual_integral G u hN)
    (WideAnchor502FinitePayment.actual_integral G u hd)
    (WideAnchor502PositiveTail.actual_integral G u hd)
theorem actual_bound_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (hN : Fintype.card V+32+4+2≤52) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u 32 4 (((51/26) : ℚ) : ℝ) := by
  exact ComputedIntegralAssembly.normalized_lower ((51/26)) (1/268435456) 128 target
    WideAnchor502Origin.payment WideAnchor502FinitePayment.payment WideAnchor502PositiveTail.payment 32 4
    (by norm_num) (by norm_num) (by norm_num [target]) budget_checked G u
    (WideAnchor502Origin.actual_integral_swapped G u hN)
    (WideAnchor502FinitePayment.actual_integral_swapped G u hd)
    (WideAnchor502PositiveTail.actual_integral_swapped G u hd)
end

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
#print axioms actual_bound_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor502OriginalAnchor
