/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMeanAnchor220FinitePayment
import Proofs.RadenkovicGutmanMeanAnchor220Origin
import Proofs.RadenkovicGutmanMeanAnchor220PositiveTail
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData

namespace Gebendorfer.RadenkovicGutman.MeanAnchor220OriginalAnchor
open CoreQuotient Set MeasureTheory
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def target : ℚ := (1555140956295688253467439833052905/32624163332060752803334972325527552)
theorem original_anchor_checked : DegreeOneMiddleAnchors.anchors[220]? =
    some (⟨52,0,0,target⟩ : DegreeOneMiddleAnchors.Anchor) := by decide +kernel

theorem budget_checked : target*(3927/1250) ≤ MeanAnchor220Origin.payment+MeanAnchor220FinitePayment.payment+
    ((25497408/3277198397) : ℚ) := by decide +kernel

/-- The exact original anchor lower bound, with its original shift and order bound. -/
theorem actual_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) (hN : Fintype.card V+2 ≤ 52) :
    (target : ℝ) ≤ ActualFusionIntegral.normalizedIntegral G u 0 0 (51/26) := by
  let f := MixedGraphIntegral.logarithm (source G u 0 0) (fused G u 0 0) (51/26)
  have hf := ActualFusionIntegral.logarithm_integrable G u 0 0 (51/26)
  have h0 := MeanAnchor220Origin.actual_integral G u hN
  have h1 := MeanAnchor220FinitePayment.actual_integral G u hd
  have hT := MeanAnchor220PositiveTail.actual_integral G u hd
  have hall := RationalIntegralPartition.three_region_lower f hf (1/16777216) 128
    (MeanAnchor220Origin.payment : ℝ) (MeanAnchor220FinitePayment.payment : ℝ) ((25497408/3277198397))
    (by norm_num) (by norm_num) h0 h1 hT
  have ht : (0 : ℝ) ≤ target := by norm_num [target]
  have hpi : Real.pi ≤ (3927/1250 : ℝ) := le_trans Real.pi_lt_d4.le (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hpi ht
  have hb : (target : ℝ)*(3927/1250) ≤
      (MeanAnchor220Origin.payment : ℝ)+(MeanAnchor220FinitePayment.payment : ℝ)+((25497408/3277198397)) := by
    norm_num [target,MeanAnchor220Origin.payment,MeanAnchor220FinitePayment.payment]
  have hi : (target : ℝ)*Real.pi ≤ ∫ y : ℝ in Ioi 0, f y := hm.trans (hb.trans hall)
  have hdiv := (le_div_iff₀ Real.pi_pos).mpr hi
  change (target : ℝ) ≤ (1/Real.pi)*(∫ y : ℝ in Ioi 0, f y)
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hdiv

#print axioms original_anchor_checked
#print axioms budget_checked
#print axioms actual_bound
end
end Gebendorfer.RadenkovicGutman.MeanAnchor220OriginalAnchor
