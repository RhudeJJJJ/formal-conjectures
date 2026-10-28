/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPositiveTail
import Proofs.RadenkovicGutmanWideAnchor030PositiveTailParts

namespace Gebendorfer.RadenkovicGutman.WideAnchor030PositiveTail
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build ((51/26)) 9 39
def K : ℚ := (995871/500000)
def Y : ℚ := 128
def payment : ℚ := (63735744/8192995871)
theorem checked : ComputedPositiveTail.checks data K Y=true := by
  simpa only [data,K,Y,WideAnchor030PositiveTailPartsData.data,WideAnchor030PositiveTailPartsData.K,WideAnchor030PositiveTailPartsData.Y] using
    WideAnchor030PositiveTailParts.checked
noncomputable section
theorem payment_checked : (payment : ℝ)=QuantitativePositiveTail.coefficient (K : ℝ) (Y : ℝ)/(Y : ℝ) := by
  norm_num [payment,K,Y,QuantitativePositiveTail.coefficient]
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (payment : ℝ)≤∫ y : ℝ in Ioi (Y : ℝ),
      MixedGraphIntegral.logarithm (source G u 9 39) (fused G u 9 39) (((51/26) : ℚ) : ℝ) y := by
  rw [payment_checked]
  exact ComputedPositiveTail.computed_actual_integral ((51/26)) 9 39 K Y checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (payment : ℝ)≤∫ y : ℝ in Ioi (Y : ℝ),
      MixedGraphIntegral.logarithm (source G u 39 9) (fused G u 39 9) (((51/26) : ℚ) : ℝ) y := by
  rw [payment_checked]
  exact ComputedPositiveTail.computed_actual_integral_swapped ((51/26)) 9 39 K Y checked G u hd
end

#print axioms checked
#print axioms payment_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor030PositiveTail
