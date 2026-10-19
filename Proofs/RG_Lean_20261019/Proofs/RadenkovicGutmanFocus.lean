/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The concrete reciprocal-coordinate coefficients and their separation from
the Schur disk, for the entire real recurrence domain.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Sections 3.1 and 4.
-/
import Proofs.RadenkovicGutmanBernstein
import Proofs.RadenkovicGutmanRootSchur

namespace Gebendorfer.RadenkovicGutman.Focus

noncomputable section

def z (y : ℝ) : ℂ := 2 + (y : ℂ) * Complex.I
def A (P Q : ℝ) : ℂ := (P * Q - 1 : ℝ) - (P + Q : ℝ) * Complex.I
def N₀ (y P Q : ℝ) : ℂ := z y * (2 + (P + Q : ℝ) * Complex.I)
def B (y P Q : ℝ) : ℂ := (P * Q + 1 : ℝ) - (P + Q - y : ℝ) * Complex.I
def D₀ (y P Q : ℝ) : ℂ := Complex.I * z y * (P + Q - y : ℝ)
def g (d y : ℝ) : ℂ := (2 - d : ℝ) + (y + d / (2 * y) : ℝ) * Complex.I
def r (d y : ℝ) : ℝ := d / (2 * y)

def quotient (y P Q : ℝ) (ζ : ℂ) : ℂ :=
  (A P Q * ζ + N₀ y P Q) / (B y P Q * ζ + D₀ y P Q)

theorem A_ne_zero (y P Q : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q) :
    A P Q ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp [A] at hi
  linarith

theorem B_ne_zero (y P Q : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q) :
    B y P Q ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp [B] at hi
  linarith

theorem numerator_pole_im (y P Q : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q) :
    (-N₀ y P Q / A P Q).im < 0 := by
  have hnorm := Complex.normSq_pos.mpr (A_ne_zero y P Q hy hP hQ)
  have hpay : 0 < (2 * P - y) * (1 + Q ^ 2) + (2 * Q - y) * (1 + P ^ 2) := by
    have hp : 0 < 2 * P - y := by linarith
    have hq : 0 < 2 * Q - y := by linarith
    positivity
  have he : (-N₀ y P Q / A P Q).im =
      -((2 * P - y) * (1 + Q ^ 2) + (2 * Q - y) * (1 + P ^ 2)) /
        Complex.normSq (A P Q) := by
    rw [Complex.div_im]
    simp only [A, N₀, z, Complex.neg_re, Complex.neg_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [he]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hpay) hnorm

theorem denominator_pole_im (y P Q : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q) :
    (-D₀ y P Q / B y P Q).im < 0 := by
  have hp : 0 < P := lt_of_lt_of_le hy hP
  have hq : 0 < Q := lt_of_lt_of_le hy hQ
  have hh : 0 < P + Q - y := by linarith
  have hpay : 0 < 2 * (1 + P * Q) - y * (P + Q - y) := by
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hQ),
      mul_nonneg hq.le (sub_nonneg.mpr hP), sq_nonneg y]
  have hnorm := Complex.normSq_pos.mpr (B_ne_zero y P Q hy hP hQ)
  have he : (-D₀ y P Q / B y P Q).im =
      -((P + Q - y) * (2 * (1 + P * Q) - y * (P + Q - y))) /
        Complex.normSq (B y P Q) := by
    rw [Complex.div_im]
    simp only [B, D₀, z, Complex.neg_re, Complex.neg_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [he]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hh hpay)) hnorm

/-- A pole below the real axis is strictly outside every upper Schur disk. -/
theorem separation (a b center : ℂ) (radius : ℝ) (hr : 0 ≤ radius)
    (ha : a ≠ 0) (hpole : (-b / a).im ≤ 0) (hc : radius < center.im) :
    0 < Complex.normSq (a * center + b) - radius ^ 2 * Complex.normSq a := by
  have hi := Complex.im_le_norm (center - (-b / a))
  have hnorm : radius < ‖center - (-b / a)‖ := by
    simp only [Complex.sub_im] at hi
    linarith
  have hs : radius ^ 2 < Complex.normSq (center - (-b / a)) := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_lt_sq₀ hr (norm_nonneg _)).mpr hnorm
  have he : a * center + b = a * (center - (-b / a)) := by field_simp; ring
  rw [he, Complex.normSq_mul]
  have hapos := Complex.normSq_pos.mpr ha
  nlinarith [mul_pos hapos (sub_pos.mpr hs)]

theorem concrete_separation (d y P Q : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) :
    0 < Complex.normSq (B y P Q * g d y + D₀ y P Q) -
      r d y ^ 2 * Complex.normSq (B y P Q) ∧
    0 < Complex.normSq (A P Q * g d y + N₀ y P Q) -
      r d y ^ 2 * Complex.normSq (A P Q) := by
  have hr : 0 ≤ r d y := by unfold r; positivity
  have hg : r d y < (g d y).im := by
    simp only [g, r, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
    linarith
  exact ⟨separation _ _ _ _ hr (B_ne_zero y P Q hy hP hQ)
      (denominator_pole_im y P Q hy hP hQ).le hg,
    separation _ _ _ _ hr (A_ne_zero y P Q hy hP hQ)
      (numerator_pole_im y P Q hy hP hQ).le hg⟩

#print axioms numerator_pole_im
#print axioms denominator_pole_im
#print axioms concrete_separation

end
end Gebendorfer.RadenkovicGutman.Focus
