/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedIntegralAssembly

namespace Gebendorfer.RadenkovicGutman.WideAnchor280Origin
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def epsilon : ℚ := (1/268435456)
def logEpsilon : ℚ := (-242601513195981/25000000000000)
def logReciprocalB : ℚ := (-271467281447723/100000000000000)
def payment : ℚ := (-3875620002694941/2684354560000000000000)
theorem epsilon_checked : RationalLog.accepts epsilon logEpsilon 28 32=true := by decide +kernel
theorem reciprocal_checked : RationalLog.accepts (1/((15 : ℚ)^2+3)) logReciprocalB 8 32=true := by decide +kernel
theorem payment_checked : ComputedIntegralAssembly.originPayment 15 epsilon logEpsilon logReciprocalB=payment := by decide +kernel
noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hN : Fintype.card V+0+6+2≤15) :
    (payment : ℝ)≤∫ y : ℝ in (0 : ℝ)..(epsilon : ℝ),
      MixedGraphIntegral.logarithm (source G u 0 6) (fused G u 0 6) (((28/15) : ℚ) : ℝ) y := by
  have h := ComputedIntegralAssembly.origin_integral ((28/15)) epsilon logEpsilon logReciprocalB 0 6 15 28 8 32
    (by norm_num) (by norm_num [epsilon]) (by norm_num [epsilon]) epsilon_checked reciprocal_checked G u hN
  rw [payment_checked] at h
  exact h
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hN : Fintype.card V+6+0+2≤15) :
    (payment : ℝ)≤∫ y : ℝ in (0 : ℝ)..(epsilon : ℝ),
      MixedGraphIntegral.logarithm (source G u 6 0) (fused G u 6 0) (((28/15) : ℚ) : ℝ) y := by
  have h := ComputedIntegralAssembly.origin_integral ((28/15)) epsilon logEpsilon logReciprocalB 6 0 15 28 8 32
    (by norm_num) (by norm_num [epsilon]) (by norm_num [epsilon]) epsilon_checked reciprocal_checked G u hN
  rw [payment_checked] at h
  exact h
end

#print axioms epsilon_checked
#print axioms reciprocal_checked
#print axioms payment_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor280Origin
