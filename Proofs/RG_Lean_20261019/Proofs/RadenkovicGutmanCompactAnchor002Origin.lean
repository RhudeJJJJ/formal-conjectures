/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCompactAnchor000Origin
namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Origin
open Set MeasureTheory CoreQuotient
open scoped Classical
noncomputable section
abbrev epsilon := CompactAnchor000Origin.epsilon
abbrev payment := CompactAnchor000Origin.payment
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hN : Fintype.card V+9+11+2≤52) :
    (payment : ℝ)≤∫ y : ℝ in (0 : ℝ)..(epsilon : ℝ),
      MixedGraphIntegral.logarithm (source G u 9 11) (fused G u 9 11) ((51/26 : ℚ) : ℝ) y := by
  have h := ComputedIntegralAssembly.origin_integral (51/26) epsilon CompactAnchor000Origin.logEpsilon CompactAnchor000Origin.logReciprocalB 9 11 52 28 12 32
    (by norm_num) (by norm_num [epsilon,CompactAnchor000Origin.epsilon])
    (by norm_num [epsilon,CompactAnchor000Origin.epsilon])
    CompactAnchor000Origin.epsilon_checked CompactAnchor000Origin.reciprocal_checked G u hN
  rw [CompactAnchor000Origin.payment_checked] at h
  exact h
#print axioms actual_integral
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hN : Fintype.card V+11+9+2≤52) :
    (payment : ℝ)≤∫ y : ℝ in (0 : ℝ)..(epsilon : ℝ),
      MixedGraphIntegral.logarithm (source G u 11 9) (fused G u 11 9) ((51/26 : ℚ) : ℝ) y := by
  have h := ComputedIntegralAssembly.origin_integral (51/26) epsilon CompactAnchor000Origin.logEpsilon CompactAnchor000Origin.logReciprocalB 11 9 52 28 12 32
    (by norm_num) (by norm_num [epsilon,CompactAnchor000Origin.epsilon])
    (by norm_num [epsilon,CompactAnchor000Origin.epsilon])
    CompactAnchor000Origin.epsilon_checked CompactAnchor000Origin.reciprocal_checked G u hN
  rw [CompactAnchor000Origin.payment_checked] at h
  exact h
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Origin
