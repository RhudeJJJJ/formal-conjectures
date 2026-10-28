/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPositiveTail
import Proofs.RadenkovicGutmanWideAnchor514PositiveTailParts

namespace Gebendorfer.RadenkovicGutman.WideAnchor514PositiveTail
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build ((51/26)) 4 44
def K : ℚ := (995871/500000)
def Y : ℚ := 128
def payment : ℚ := (63735744/8192995871)
theorem checked : ComputedPositiveTail.checks data K Y=true := by
  simpa only [data,K,Y,WideAnchor514PositiveTailPartsData.data,WideAnchor514PositiveTailPartsData.K,WideAnchor514PositiveTailPartsData.Y] using
    WideAnchor514PositiveTailParts.checked
noncomputable section
theorem payment_checked : (payment : ℝ)=QuantitativePositiveTail.coefficient (K : ℝ) (Y : ℝ)/(Y : ℝ) := by
  norm_num [payment,K,Y,QuantitativePositiveTail.coefficient]
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (payment : ℝ)≤∫ y : ℝ in Ioi (Y : ℝ),
      MixedGraphIntegral.logarithm (source G u 4 44) (fused G u 4 44) (((51/26) : ℚ) : ℝ) y := by
  rw [payment_checked]
  exact ComputedPositiveTail.computed_actual_integral ((51/26)) 4 44 K Y checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (payment : ℝ)≤∫ y : ℝ in Ioi (Y : ℝ),
      MixedGraphIntegral.logarithm (source G u 44 4) (fused G u 44 4) (((51/26) : ℚ) : ℝ) y := by
  rw [payment_checked]
  exact ComputedPositiveTail.computed_actual_integral_swapped ((51/26)) 4 44 K Y checked G u hd
end

#print axioms checked
#print axioms payment_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor514PositiveTail
