/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The Hermitian resolvent disk used by the arbitrary-core Schur reduction.
No integral sign estimate or global energy inequality is asserted here.
-/
import Proofs.RadenkovicGutmanPathResolvent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Gebendorfer.RadenkovicGutman.ResolventDisk

open Matrix
open scoped InnerProductSpace

theorem scalar_disk (q : ℂ) (d t y : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hcs : Complex.normSq q ≤ d * t) (him : q.im = -y * t) :
    ‖q + (d / (2 * y) : ℝ) * Complex.I‖ ≤ d / (2 * y) := by
  have hr : 0 ≤ d / (2 * y) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hr).mp
  rw [Complex.sq_norm]
  have hpay : q.im * (2 * (d / (2 * y))) = -(d * t) := by
    rw [him]
    field_simp
  simp only [Complex.normSq_apply, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self,
    add_zero, Complex.add_im, Complex.mul_im] at *
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Cauchy--Schwarz and the imaginary resolvent identity give the disk directly. -/
theorem disk_of_equation (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (z : ℂ) (hz : 0 < z.im) (b x : E) (hx : z • x - T x = b) :
    ‖⟪b, x⟫_ℂ + (‖b‖ ^ 2 / (2 * z.im) : ℝ) * Complex.I‖ ≤
      ‖b‖ ^ 2 / (2 * z.im) := by
  have him : (⟪b, x⟫_ℂ).im = -z.im * ‖x‖ ^ 2 := by
    rw [← hx, inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
    have ht := hT.im_inner_apply_self x
    change (⟪T x, x⟫_ℂ).im = 0 at ht
    simp [← Complex.ofReal_pow, ht]
  have hnorm := norm_inner_le_norm (𝕜 := ℂ) b x
  have hcs : Complex.normSq (⟪b, x⟫_ℂ) ≤ ‖b‖ ^ 2 * ‖x‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (⟪b, x⟫_ℂ), norm_nonneg b, norm_nonneg x]
  exact scalar_disk _ _ _ _ (sq_nonneg _) hz hcs him

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A disk bound on the actual inverse of every nonreal Hermitian shift. -/
theorem hermitian_resolvent_disk (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (b : V → ℂ) :
    ‖star b ⬝ᵥ ((z • (1 : Matrix V V ℂ) - H)⁻¹ *ᵥ b) +
      (‖(WithLp.toLp 2 b : EuclideanSpace ℂ V)‖ ^ 2 / (2 * z.im) : ℝ) * Complex.I‖ ≤
      ‖(WithLp.toLp 2 b : EuclideanSpace ℂ V)‖ ^ 2 / (2 * z.im) := by
  let M := z • (1 : Matrix V V ℂ) - H
  let x : EuclideanSpace ℂ V := WithLp.toLp 2 (M⁻¹ *ᵥ b)
  let B : EuclideanSpace ℂ V := WithLp.toLp 2 b
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr
    (PathRecurrence.shifted_det_ne_zero H hH z hz.ne')
  have hvec : (z • (M⁻¹ *ᵥ b)) - H *ᵥ (M⁻¹ *ᵥ b) = b := by
    have h : M *ᵥ (M⁻¹ *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]
    dsimp only [M] at h
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact h
  have hx : z • x - H.toEuclideanLin x = B := by
    ext i
    exact congrFun hvec i
  have h := disk_of_equation H.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) z hz B x hx
  simpa [x, B, M, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h

#print axioms disk_of_equation
#print axioms hermitian_resolvent_disk

/-- The actual Schur-complement scalar is in the predicted upper-half-plane
disk. The root diagonal is real and no property of a particular core is assumed. -/
theorem schur_complement_disk (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (d : ℝ) (b : V → ℂ) :
    let r : ℝ := ‖(WithLp.toLp 2 b : EuclideanSpace ℂ V)‖ ^ 2 / (2 * z.im)
    let q := star b ⬝ᵥ ((z • (1 : Matrix V V ℂ) - H)⁻¹ *ᵥ b)
    ‖(z - d - q) - (z - d + r * Complex.I)‖ ≤ r ∧
      z.im ≤ (z - d - q).im := by
  dsimp only
  let r : ℝ := ‖(WithLp.toLp 2 b : EuclideanSpace ℂ V)‖ ^ 2 / (2 * z.im)
  let q := star b ⬝ᵥ ((z • (1 : Matrix V V ℂ) - H)⁻¹ *ᵥ b)
  have h := hermitian_resolvent_disk H hH z hz b
  change ‖q + r * Complex.I‖ ≤ r at h
  have hi := Complex.im_le_norm (q + r * Complex.I)
  have hqi : q.im ≤ 0 := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hi
    linarith
  constructor
  · change ‖(z - d - q) - (z - d + r * Complex.I)‖ ≤ r
    have he : (z - d - q) - (z - d + r * Complex.I) = -(q + r * Complex.I) := by ring
    rw [he, norm_neg]
    exact h
  · change z.im ≤ (z - d - q).im
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    linarith

#print axioms schur_complement_disk

end Gebendorfer.RadenkovicGutman.ResolventDisk
