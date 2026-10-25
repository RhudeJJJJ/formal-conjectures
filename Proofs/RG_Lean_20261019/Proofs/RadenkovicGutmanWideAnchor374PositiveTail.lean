/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPositiveTail

namespace Gebendorfer.RadenkovicGutman.WideAnchor374PositiveTail
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build ((21/11)) 2 12
def K : ℚ := (1991713/1000000)
def Y : ℚ := 128
def payment : ℚ := (127469632/16385991713)
theorem checked : ComputedPositiveTail.checks data K Y=true := by decide +kernel
noncomputable section
theorem payment_checked : (payment : ℝ)=QuantitativePositiveTail.coefficient (K : ℝ) (Y : ℝ)/(Y : ℝ) := by
  norm_num [payment,K,Y,QuantitativePositiveTail.coefficient]
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (payment : ℝ)≤∫ y : ℝ in Ioi (Y : ℝ),
      MixedGraphIntegral.logarithm (source G u 2 12) (fused G u 2 12) (((21/11) : ℚ) : ℝ) y := by
  rw [payment_checked]
  exact ComputedPositiveTail.computed_actual_integral ((21/11)) 2 12 K Y checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (payment : ℝ)≤∫ y : ℝ in Ioi (Y : ℝ),
      MixedGraphIntegral.logarithm (source G u 12 2) (fused G u 12 2) (((21/11) : ℚ) : ℝ) y := by
  rw [payment_checked]
  exact ComputedPositiveTail.computed_actual_integral_swapped ((21/11)) 2 12 K Y checked G u hd
end

#print axioms checked
#print axioms payment_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor374PositiveTail
