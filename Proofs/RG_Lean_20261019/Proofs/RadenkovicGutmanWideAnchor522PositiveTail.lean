/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPositiveTail

namespace Gebendorfer.RadenkovicGutman.WideAnchor522PositiveTail
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build ((23/12)) 4 6
def K : ℚ := (995859/500000)
def Y : ℚ := 128
def payment : ℚ := (63734976/8192995859)
theorem checked : ComputedPositiveTail.checks data K Y=true := by decide +kernel
noncomputable section
theorem payment_checked : (payment : ℝ)=QuantitativePositiveTail.coefficient (K : ℝ) (Y : ℝ)/(Y : ℝ) := by
  norm_num [payment,K,Y,QuantitativePositiveTail.coefficient]
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (payment : ℝ)≤∫ y : ℝ in Ioi (Y : ℝ),
      MixedGraphIntegral.logarithm (source G u 4 6) (fused G u 4 6) (((23/12) : ℚ) : ℝ) y := by
  rw [payment_checked]
  exact ComputedPositiveTail.computed_actual_integral ((23/12)) 4 6 K Y checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (payment : ℝ)≤∫ y : ℝ in Ioi (Y : ℝ),
      MixedGraphIntegral.logarithm (source G u 6 4) (fused G u 6 4) (((23/12) : ℚ) : ℝ) y := by
  rw [payment_checked]
  exact ComputedPositiveTail.computed_actual_integral_swapped ((23/12)) 4 6 K Y checked G u hd
end

#print axioms checked
#print axioms payment_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor522PositiveTail
