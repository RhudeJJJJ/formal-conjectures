/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedIntegralAssembly

namespace Gebendorfer.RadenkovicGutman.WideAnchor516Origin
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def epsilon : ℚ := (1/268435456)
def logEpsilon : ℚ := (-242601513195981/25000000000000)
def logReciprocalB : ℚ := (-65206211275587/20000000000000)
def payment : ℚ := (-17503682419104167/6710886400000000000000)
theorem epsilon_checked : RationalLog.accepts epsilon logEpsilon 28 32=true := by decide +kernel
theorem reciprocal_checked : RationalLog.accepts (1/((26 : ℚ)^2+3)) logReciprocalB 10 32=true := by decide +kernel
theorem payment_checked : ComputedIntegralAssembly.originPayment 26 epsilon logEpsilon logReciprocalB=payment := by decide +kernel
noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hN : Fintype.card V+4+4+2≤26) :
    (payment : ℝ)≤∫ y : ℝ in (0 : ℝ)..(epsilon : ℝ),
      MixedGraphIntegral.logarithm (source G u 4 4) (fused G u 4 4) (((25/13) : ℚ) : ℝ) y := by
  have h := ComputedIntegralAssembly.origin_integral ((25/13)) epsilon logEpsilon logReciprocalB 4 4 26 28 10 32
    (by norm_num) (by norm_num [epsilon]) (by norm_num [epsilon]) epsilon_checked reciprocal_checked G u hN
  rw [payment_checked] at h
  exact h
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hN : Fintype.card V+4+4+2≤26) :
    (payment : ℝ)≤∫ y : ℝ in (0 : ℝ)..(epsilon : ℝ),
      MixedGraphIntegral.logarithm (source G u 4 4) (fused G u 4 4) (((25/13) : ℚ) : ℝ) y := by
  have h := ComputedIntegralAssembly.origin_integral ((25/13)) epsilon logEpsilon logReciprocalB 4 4 26 28 10 32
    (by norm_num) (by norm_num [epsilon]) (by norm_num [epsilon]) epsilon_checked reciprocal_checked G u hN
  rw [payment_checked] at h
  exact h
end

#print axioms epsilon_checked
#print axioms reciprocal_checked
#print axioms payment_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor516Origin
