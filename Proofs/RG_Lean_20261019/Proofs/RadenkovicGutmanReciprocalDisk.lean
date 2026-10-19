/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Circle inversion for the genuine reciprocal Schur disk.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Section 3.1.
-/
import Proofs.RadenkovicGutmanResolventDisk
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Gebendorfer.RadenkovicGutman.ResolventDisk

/-- Inversion of a closed disk that excludes zero. -/
theorem inverse_disk (g w : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hsep : 0 < Complex.normSq g - r ^ 2) (hw : ‖w - g‖ ≤ r) :
    w ≠ 0 ∧
      ‖w⁻¹ - star g / (Complex.normSq g - r ^ 2 : ℝ)‖ ≤
        r / (Complex.normSq g - r ^ 2) := by
  let δ := Complex.normSq g - r ^ 2
  have hδ : 0 < δ := hsep
  have hd0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  have hw2 : Complex.normSq (w - g) ≤ r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hw0 : w ≠ 0 := by
    intro hz
    simp only [hz, zero_sub, Complex.normSq_neg] at hw2
    dsimp [δ] at hδ
    linarith
  refine ⟨hw0, ?_⟩
  have hN : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
  have hid : Complex.normSq ((δ : ℂ) - w * star g) - r ^ 2 * Complex.normSq w =
      δ * (Complex.normSq (w - g) - r ^ 2) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    dsimp [δ]
    simp only [Complex.normSq_apply]
    ring
  have hle : Complex.normSq ((δ : ℂ) - w * star g) ≤ r ^ 2 * Complex.normSq w := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hw2)]
  have he : w⁻¹ - star g / (δ : ℂ) = ((δ : ℂ) - w * star g) / (w * (δ : ℂ)) := by
    field_simp
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg hr hδ.le)).mp
  rw [Complex.sq_norm, he, Complex.normSq_div, Complex.normSq_mul,
    Complex.normSq_ofReal]
  rw [div_pow]
  simp only [← pow_two]
  exact (div_le_div_iff₀ (mul_pos hN (sq_pos_of_pos hδ))
    (sq_pos_of_pos hδ)).mpr (by nlinarith [mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hle)])

/-- The explicit reciprocal disk in Lemma 3.1, including its normalization. -/
theorem reciprocal_schur_disk (d y : ℝ) (hd : 0 ≤ d) (hy : 0 < y) (ζ : ℂ)
    (hζ : ‖ζ - ((2 - d : ℝ) + (y + d / (2 * y) : ℝ) * Complex.I)‖ ≤
      d / (2 * y)) :
    let Δ := (d - 2) ^ 2 + d + y ^ 2
    let c : ℂ := ((2 - d) / Δ : ℝ) - ((2 * y ^ 2 + d) / (2 * y * Δ) : ℝ) * Complex.I
    let R : ℝ := d / (2 * y * Δ)
    ζ ≠ 0 ∧ ‖ζ⁻¹ - c‖ ≤ R ∧ Complex.normSq c - R ^ 2 = 1 / Δ := by
  dsimp only
  let Δ := (d - 2) ^ 2 + d + y ^ 2
  let g : ℂ := ((2 - d : ℝ) + (y + d / (2 * y) : ℝ) * Complex.I)
  let r := d / (2 * y)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hg : Complex.normSq g - r ^ 2 = Δ := by
    dsimp [g, r, Δ]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    field_simp
    ring
  have hinv := inverse_disk g ζ r (by dsimp [r]; positivity) (hg ▸ hΔ) hζ
  have hc : star g / (Δ : ℂ) =
      (((2 - d) / Δ : ℝ) - ((2 * y ^ 2 + d) / (2 * y * Δ) : ℝ) * Complex.I) := by
    dsimp [g]
    apply Complex.ext <;>
      simp only [Complex.div_re, Complex.div_im, Complex.normSq_ofReal,
        Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
        add_zero, zero_add, mul_zero, mul_one, sub_zero] <;> field_simp <;> ring
  rw [hg, hc] at hinv
  refine ⟨hinv.1, ?_, ?_⟩
  · simpa only [r, div_div] using hinv.2
  · rw [← hc]
    rw [Complex.normSq_div, show Complex.normSq (star g) = Complex.normSq g from
      Complex.normSq_conj g, Complex.normSq_ofReal]
    have hrel : Complex.normSq g = Δ + r ^ 2 := by linarith
    rw [hrel]
    dsimp [r]
    field_simp
    ring

#print axioms inverse_disk
#print axioms reciprocal_schur_disk

end Gebendorfer.RadenkovicGutman.ResolventDisk
