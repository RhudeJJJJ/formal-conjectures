/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedIntegralAssembly

namespace Gebendorfer.RadenkovicGutman.WideAnchor374Origin
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def epsilon : ℚ := (1/268435456)
def logEpsilon : ℚ := (-242601513195981/25000000000000)
def logReciprocalB : ℚ := (-30941320615413/10000000000000)
def payment : ℚ := (-7314005924159297/3355443200000000000000)
theorem epsilon_checked : RationalLog.accepts epsilon logEpsilon 28 32=true := by decide +kernel
theorem reciprocal_checked : RationalLog.accepts (1/((22 : ℚ)^2+3)) logReciprocalB 9 32=true := by decide +kernel
theorem payment_checked : ComputedIntegralAssembly.originPayment 22 epsilon logEpsilon logReciprocalB=payment := by decide +kernel
noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hN : Fintype.card V+2+12+2≤22) :
    (payment : ℝ)≤∫ y : ℝ in (0 : ℝ)..(epsilon : ℝ),
      MixedGraphIntegral.logarithm (source G u 2 12) (fused G u 2 12) (((21/11) : ℚ) : ℝ) y := by
  have h := ComputedIntegralAssembly.origin_integral ((21/11)) epsilon logEpsilon logReciprocalB 2 12 22 28 9 32
    (by norm_num) (by norm_num [epsilon]) (by norm_num [epsilon]) epsilon_checked reciprocal_checked G u hN
  rw [payment_checked] at h
  exact h
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hN : Fintype.card V+12+2+2≤22) :
    (payment : ℝ)≤∫ y : ℝ in (0 : ℝ)..(epsilon : ℝ),
      MixedGraphIntegral.logarithm (source G u 12 2) (fused G u 12 2) (((21/11) : ℚ) : ℝ) y := by
  have h := ComputedIntegralAssembly.origin_integral ((21/11)) epsilon logEpsilon logReciprocalB 12 2 22 28 9 32
    (by norm_num) (by norm_num [epsilon]) (by norm_num [epsilon]) epsilon_checked reciprocal_checked G u hN
  rw [payment_checked] at h
  exact h
end

#print axioms epsilon_checked
#print axioms reciprocal_checked
#print axioms payment_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end Gebendorfer.RadenkovicGutman.WideAnchor374Origin
