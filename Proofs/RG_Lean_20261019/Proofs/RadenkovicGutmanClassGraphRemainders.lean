/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanClassScalarIntegrals
import Proofs.RadenkovicGutmanOriginBound
import Proofs.RadenkovicGutmanUniformTail
import Proofs.RadenkovicGutmanConcreteGraphQuotient

namespace Gebendorfer.RadenkovicGutman.ClassGraphRemainders
open CoreQuotient Focus PathEnclosure Set MeasureTheory ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem actual_logarithm (C : SimpleGraph V) (u : V) (p q : ℕ)
    (y : ℝ) (hy : 0 < y) :
    MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y=
      Real.log ‖quotient y (rho y p) (rho y q) (RootSchur.schurScalar C u (z y))‖ := by
  change Real.log ‖(shifted (z y) (source C u p q)).det /
    (shifted (z y) (fused C u p q)).det‖ = _
  rw [concrete_graph_quotient C u y hy p q]

theorem origin_pointwise (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hd : 1 ≤ C.degree u) (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    ClassScalarIntegrals.origin y ≤
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  have hd0 : (0 : ℝ) < C.degree u := by exact_mod_cast (by omega : 0 < C.degree u)
  rw [ClassScalarIntegrals.origin_eq y hy,actual_logarithm C u p q y hy]
  exact OriginBound.logarithm_lower _ y _ _ hd0 hy hy1 (rho_ge y hy p) (rho_ge y hy q)
    _ (schur_in_disk C u y hy).1

theorem tail_pointwise (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hd : 1 ≤ C.degree u) (y : ℝ) (hy : 1 ≤ y) :
    ClassScalarIntegrals.tail y ≤
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  have hy0 : 0 < y := by linarith
  have hdr : (1 : ℝ) ≤ C.degree u := by exact_mod_cast hd
  rw [ClassScalarIntegrals.tail_eq,actual_logarithm C u p q y hy0]
  exact UniformTail.actual_log_lower _ y (arm y p) (arm y q) hdr hy
    ⟨arm_nonneg y p,arm_le_one y hy0 p⟩ ⟨arm_nonneg y q,arm_le_one y hy0 q⟩
    _ (schur_in_disk C u y hy0).1

theorem origin_integral_lower (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hd : 1 ≤ C.degree u) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    a*(Real.log (2*a/5)-1) ≤ ∫ y : ℝ in (0 : ℝ)..a,
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  apply ClassScalarIntegrals.origin_lower _ (logarithm_integrable C u p q 2) a ha
  intro y hy
  exact origin_pointwise C u p q hd y hy.1 (hy.2.trans ha1)

theorem tail_integral_lower (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hd : 1 ≤ C.degree u) (Y : ℝ) (hY : 1 ≤ Y) :
    -1/(2*Y) ≤ ∫ y : ℝ in Ioi Y,
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  apply ClassScalarIntegrals.tail_lower _ (logarithm_integrable C u p q 2) Y (by linarith)
  intro y hy
  exact tail_pointwise C u p q hd y (hY.trans hy.le)

/-- The finite interval payment is the sole remaining premise. Both infinite
endpoint regions are already attached to the same actual Laplace matrices. -/
theorem normalized_lower_of_finite_payment (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hd : 1 ≤ C.degree u) (a Y B : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hY : 1 ≤ Y)
    (hfinite : B ≤ ∫ y : ℝ in a..Y,
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y) :
    (a*(Real.log (2*a/5)-1)+B-1/(2*Y))/Real.pi ≤ normalizedIntegral C u p q 2 := by
  let f := MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2
  have hf := logarithm_integrable C u p q 2
  have hay : a ≤ Y := by linarith
  have h₀ := origin_integral_lower C u p q hd a ha ha1
  have htail := tail_integral_lower C u p q hd Y hY
  rw [neg_div] at htail
  have hsplit₀ := intervalIntegral.integral_Ioi_sub_Ioi hf ha.le
  have hsplit₁ := intervalIntegral.integral_Ioi_sub_Ioi
    (hf.mono_set (Ioi_subset_Ioi ha.le)) hay
  have hall : a*(Real.log (2*a/5)-1)+B-1/(2*Y) ≤ ∫ y : ℝ in Ioi 0, f y := by
    dsimp [f]
    linarith only [h₀,htail,hfinite,hsplit₀,hsplit₁]
  change _ ≤ (1/Real.pi)*(∫ y : ℝ in Ioi 0, f y)
  calc
    _ = (1/Real.pi)*(a*(Real.log (2*a/5)-1)+B-1/(2*Y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hall (by positivity)

#print axioms actual_logarithm
#print axioms origin_pointwise
#print axioms tail_pointwise
#print axioms origin_integral_lower
#print axioms tail_integral_lower
#print axioms normalized_lower_of_finite_payment
end
end Gebendorfer.RadenkovicGutman.ClassGraphRemainders
