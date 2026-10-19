/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The actual graph characteristic determinants for an arbitrary core and all
positive arm lengths. This module does not prove an energy comparison.
-/
import Proofs.RadenkovicGutmanGraphJoin

namespace Gebendorfer.RadenkovicGutman.CoreQuotient

open Matrix Finset
open scoped Classical
noncomputable section

open Gebendorfer.RadenkovicGutman.PathRecurrence

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem shifted_path (z : ℂ) (n : ℕ) :
    shifted z (SimpleGraph.pathGraph n) = pathMatrix z n := by
  unfold shifted pathMatrix
  congr 3

/-- Core with two prescribed pendant paths; p and q denote lengths minus one. -/
def source (C : SimpleGraph V) (u : V) (p q : ℕ) :
    SimpleGraph (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) :=
  joinTwo C (SimpleGraph.pathGraph (p + 1)) (SimpleGraph.pathGraph (q + 1)) u 0 0

/-- The fused graph, with the combined path relabelled from its attachment endpoint. -/
def fused (C : SimpleGraph V) (u : V) (p q : ℕ) :
    SimpleGraph (V ⊕ Fin (p + q + 2)) :=
  join C (SimpleGraph.pathGraph (p + q + 2)) u 0

def rootResolvent (z : ℂ) (C : SimpleGraph V) (u : V) : ℂ :=
  (shifted z C)⁻¹ u u

theorem shifted_isUnit (z : ℂ) (hz : z.im ≠ 0) (C : SimpleGraph V) :
    IsUnit (shifted z C).det := by
  exact isUnit_iff_ne_zero.mpr
    (shifted_det_ne_zero _ (C.isHermitian_lapMatrix ℂ) z hz)

theorem source_det (z : ℂ) (hz : z.im ≠ 0)
    (C : SimpleGraph V) (u : V) (p q : ℕ) :
    (shifted z (source C u p q)).det = (shifted z C).det *
      ((den z (p + 1) - num z (p + 1)) *
        (den z (q + 1) - num z (q + 1)) -
        rootResolvent z C u * (2 * den z (p + 1) * den z (q + 1) -
          num z (p + 1) * den z (q + 1) - num z (q + 1) * den z (p + 1))) := by
  unfold source
  rw [shifted_joinTwo, rooted_two_arm_det _ _ _ (shifted_isUnit z hz C)
    (shifted_isUnit z hz _) (shifted_isUnit z hz _)]
  rw [shifted_path, shifted_path]
  change (shifted z C).det * (pathMatrix z (p + 1)).det *
    (pathMatrix z (q + 1)).det *
    ((1 - (pathMatrix z (p + 1))⁻¹ 0 0) *
      (1 - (pathMatrix z (q + 1))⁻¹ 0 0) -
      rootResolvent z C u *
        (2 - (pathMatrix z (p + 1))⁻¹ 0 0 - (pathMatrix z (q + 1))⁻¹ 0 0)) = _
  rw [pathMatrix_det, pathMatrix_det, pathMatrix_inv_endpoint, pathMatrix_inv_endpoint]
  unfold resolventQuotient
  have hp := den_ne_zero_of_im_ne_zero z hz p
  have hq := den_ne_zero_of_im_ne_zero z hz q
  field_simp

theorem fused_det (z : ℂ) (hz : z.im ≠ 0)
    (C : SimpleGraph V) (u : V) (p q : ℕ) :
    (shifted z (fused C u p q)).det = (shifted z C).det *
      (den z (p + q + 2) - num z (p + q + 2) -
        rootResolvent z C u * den z (p + q + 2)) := by
  unfold fused
  rw [shifted_join, rooted_one_arm_det _ _ (shifted_isUnit z hz C)
    (shifted_isUnit z hz _)]
  rw [shifted_path]
  change (shifted z C).det * (pathMatrix z ((p + q + 1) + 1)).det *
    (1 - rootResolvent z C u - (pathMatrix z ((p + q + 1) + 1))⁻¹ 0 0) = _
  rw [pathMatrix_det, pathMatrix_inv_endpoint]
  unfold resolventQuotient
  have hr := den_ne_zero_of_im_ne_zero z hz (p + q + 1)
  field_simp
  ring

#print axioms source_det
#print axioms fused_det

def twoArmFactor (z : ℂ) (p q : ℕ) (k : ℂ) : ℂ :=
  (den z (p + 1) - num z (p + 1)) * (den z (q + 1) - num z (q + 1)) -
    k * (2 * den z (p + 1) * den z (q + 1) -
      num z (p + 1) * den z (q + 1) - num z (q + 1) * den z (p + 1))

def oneArmFactor (z : ℂ) (p q : ℕ) (k : ℂ) : ℂ :=
  den z (p + q + 2) - num z (p + q + 2) - k * den z (p + q + 2)

theorem singleton_factor_calibration (z : ℂ) (hz : z ≠ 0) (p q : ℕ) :
    twoArmFactor z p q (1 / z) = oneArmFactor z p q (1 / z) ∧
    z * twoArmFactor z p q (1 / z) = den z (p + q + 3) := by
  have h := singleton_normalization z (p + 1) (q + 1)
  have he : (p + 1) + (q + 1) = p + q + 2 := by omega
  rw [he] at h
  constructor
  · unfold twoArmFactor oneArmFactor
    field_simp
    linear_combination h
  · unfold twoArmFactor
    have hd := den_succ z (p + q + 2)
    rw [show p + q + 2 + 1 = p + q + 3 by omega] at hd
    field_simp
    linear_combination h - hd

/-- The normalized quotient, with the cancelling path factors kept polynomial.
All matrices in this statement are the actual graph Laplacian shifts. -/
theorem normalized_determinant_quotient (z : ℂ) (hz : z.im ≠ 0)
    (C : SimpleGraph V) (u : V) (p q : ℕ) :
    (shifted z (source C u p q)).det / (shifted z (fused C u p q)).det =
      (twoArmFactor z p q (rootResolvent z C u) / twoArmFactor z p q (1 / z)) *
      (oneArmFactor z p q (1 / z) / oneArmFactor z p q (rootResolvent z C u)) := by
  have hz0 : z ≠ 0 := by intro h; apply hz; simp [h]
  have hcal := singleton_factor_calibration z hz0 p q
  have hnext := den_ne_zero_of_im_ne_zero z hz (p + q + 2)
  have hf0 : twoArmFactor z p q (1 / z) ≠ 0 := by
    intro he
    apply hnext
    rw [show p + q + 2 + 1 = p + q + 3 by omega, ← hcal.2, he, mul_zero]
  have hc : (shifted z C).det ≠ 0 := (shifted_isUnit z hz C).ne_zero
  have hg : oneArmFactor z p q (rootResolvent z C u) ≠ 0 := by
    have hn := (shifted_isUnit z hz (fused C u p q)).ne_zero
    rw [fused_det z hz] at hn
    exact (mul_ne_zero_iff.mp hn).2
  rw [source_det z hz, fused_det z hz]
  change ((shifted z C).det * twoArmFactor z p q (rootResolvent z C u)) /
    ((shifted z C).det * oneArmFactor z p q (rootResolvent z C u)) = _
  rw [← hcal.1]
  field_simp

#print axioms singleton_factor_calibration
#print axioms normalized_determinant_quotient

theorem twoArmFactor_resolvents (z : ℂ) (hz : z.im ≠ 0) (p q : ℕ) (k : ℂ) :
    twoArmFactor z p q k = den z (p + 1) * den z (q + 1) *
      ((1 - resolventQuotient z (p + 1)) * (1 - resolventQuotient z (q + 1)) -
        k * (2 - resolventQuotient z (p + 1) - resolventQuotient z (q + 1))) := by
  have hp := den_ne_zero_of_im_ne_zero z hz p
  have hq := den_ne_zero_of_im_ne_zero z hz q
  unfold twoArmFactor resolventQuotient
  field_simp

theorem oneArmFactor_resolvent (z : ℂ) (hz : z.im ≠ 0) (p q : ℕ) (k : ℂ) :
    oneArmFactor z p q k = den z (p + q + 2) *
      (1 - resolventQuotient z (p + q + 2) - k) := by
  have hr := den_ne_zero_of_im_ne_zero z hz (p + q + 1)
  unfold oneArmFactor resolventQuotient
  field_simp

/-- Lemma 2.2 of the manuscript, in precisely its endpoint-resolvent form. -/
theorem normalized_resolvent_quotient (z : ℂ) (hz : z.im ≠ 0)
    (C : SimpleGraph V) (u : V) (p q : ℕ) :
    let hp := resolventQuotient z (p + 1)
    let hq := resolventQuotient z (q + 1)
    let hr := resolventQuotient z (p + q + 2)
    let k := rootResolvent z C u
    let A₀ := (1 - hp) * (1 - hq)
    let B₀ := 2 - hp - hq
    let C₀ := 1 - hr
    (shifted z (source C u p q)).det / (shifted z (fused C u p q)).det =
      ((A₀ - B₀ * k) / (A₀ - B₀ * (1 / z))) *
      ((C₀ - 1 / z) / (C₀ - k)) := by
  dsimp only
  rw [normalized_determinant_quotient z hz C u p q]
  simp_rw [twoArmFactor_resolvents z hz, oneArmFactor_resolvent z hz]
  have hpq := mul_ne_zero (den_ne_zero_of_im_ne_zero z hz p)
    (den_ne_zero_of_im_ne_zero z hz q)
  have hr := den_ne_zero_of_im_ne_zero z hz (p + q + 1)
  rw [mul_div_mul_left _ _ hpq, mul_div_mul_left _ _ hr]
  ring

#print axioms normalized_resolvent_quotient

end
end Gebendorfer.RadenkovicGutman.CoreQuotient
