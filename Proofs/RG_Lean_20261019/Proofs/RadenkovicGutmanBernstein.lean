/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Sound coefficient inequalities in a common tensor Bernstein basis.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Lemma 4.2. This module does not assert acceptance or
exhaustive coverage of the manuscript's concrete certificates.
-/
import Proofs.RadenkovicGutmanMobiusDisk
import Mathlib.RingTheory.Polynomial.Bernstein

namespace Gebendorfer.RadenkovicGutman.Bernstein

open Finset
open scoped Classical
noncomputable section

def basis (n : ℕ) (j : Fin (n + 1)) (x : ℝ) : ℝ :=
  (bernsteinPolynomial ℝ n j).eval x

theorem basis_nonneg (n : ℕ) (j : Fin (n + 1)) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    0 ≤ basis n j x := by
  unfold basis bernsteinPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  have hx0 := hx.1
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  positivity

theorem basis_sum (n : ℕ) (x : ℝ) : ∑ j : Fin (n + 1), basis n j x = 1 := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)
  unfold basis
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (bernsteinPolynomial ℝ n j).eval x) (n + 1)]
  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_one, basis] using h

variable {K : Type*} [Fintype K]

def tensor (n : K → ℕ) (j : ∀ i, Fin (n i + 1)) (x : K → ℝ) : ℝ :=
  ∏ i, basis (n i) (j i) (x i)

theorem tensor_nonneg (n : K → ℕ) (j : ∀ i, Fin (n i + 1)) (x : K → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc 0 1) : 0 ≤ tensor n j x := by
  exact Finset.prod_nonneg (fun i _ => basis_nonneg _ _ _ (hx i))

theorem tensor_sum (n : K → ℕ) (x : K → ℝ) :
    ∑ j : ∀ i, Fin (n i + 1), tensor n j x = 1 := by
  have h := Fintype.prod_sum (fun i (j : Fin (n i + 1)) => basis (n i) j (x i))
  simp only [basis_sum, Finset.prod_const_one] at h
  exact h.symm

/-- A common nonnegative basis preserves every coefficientwise lower inequality. -/
theorem weighted_ratio {J : Type*} [Fintype J] (w p q : J → ℝ) (L : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hq : 0 < ∑ j, q j * w j)
    (hcoeff : ∀ j, L * q j ≤ p j) :
    L ≤ (∑ j, p j * w j) / (∑ j, q j * w j) := by
  apply (le_div_iff₀ hq).mpr
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  nlinarith [mul_nonneg (sub_nonneg.mpr (hcoeff j)) (hw j)]

theorem tensor_denominator_pos (n : K → ℕ) (q : (∀ i, Fin (n i + 1)) → ℝ)
    (x : K → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) (hq : ∀ j, 0 < q j) :
    0 < ∑ j, q j * tensor n j x := by
  have hs := tensor_sum n x
  have hw := tensor_nonneg n
  have hex : ∃ j, 0 < tensor n j x := by
    by_contra! h
    have hz : ∑ j, tensor n j x ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
    linarith
  obtain ⟨j, hj⟩ := hex
  apply (Finset.sum_pos_iff_of_nonneg (fun j _ =>
    mul_nonneg (hq j).le (hw j x hx))).mpr
  exact ⟨j, Finset.mem_univ _, mul_pos (hq j) hj⟩

theorem tensor_ratio (n : K → ℕ) (p q : (∀ i, Fin (n i + 1)) → ℝ)
    (x : K → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) (L : ℝ)
    (hq : ∀ j, 0 < q j) (hcoeff : ∀ j, L * q j ≤ p j) :
    L ≤ (∑ j, p j * tensor n j x) / (∑ j, q j * tensor n j x) :=
  weighted_ratio _ _ _ L (fun j => tensor_nonneg n j x hx)
    (tensor_denominator_pos n q x hx hq) hcoeff

/-- The positive rational Young parameter gives the manuscript's common denominator. -/
theorem young_denominator (u v c : ℝ) (hc : 0 < c) :
    (u + v) ^ 2 ≤ (1 + c) * u ^ 2 + (1 + 1 / c) * v ^ 2 := by
  have h := sq_nonneg (c * u - v)
  have hp := mul_pos hc hc
  apply (mul_le_mul_iff_right₀ hc).mp
  field_simp
  nlinarith

/-- Coefficient acceptance implies the squared norm bound once the exact common
polynomial representation has been supplied. -/
theorem mobius_certificate (a b c d η : ℂ)
    (hE : 0 < Complex.normSq d - Complex.normSq c)
    (hN : 0 < Complex.normSq b - Complex.normSq a) (hη : ‖η‖ ≤ 1)
    (s L : ℝ) (hs : 0 < s)
    (hL : L * ((1 + s) * ‖b * star d - a * star c‖ ^ 2 +
      (1 + 1 / s) * ‖a * d - b * c‖ ^ 2) ≤
        (Complex.normSq b - Complex.normSq a) ^ 2) :
    L ≤ ‖(a * η + b) / (c * η + d)‖ ^ 2 := by
  let N := Complex.normSq b - Complex.normSq a
  let U := ‖b * star d - a * star c‖
  let V := ‖a * d - b * c‖
  let f := ‖(a * η + b) / (c * η + d)‖
  let D := (1 + s) * U ^ 2 + (1 + 1 / s) * V ^ 2
  have hid : U ^ 2 - V ^ 2 = (Complex.normSq d - Complex.normSq c) * N :=
    MobiusDisk.center_distance_identity a b c d
  have hsep : V < U := by
    have hp := mul_pos hE hN
    nlinarith [norm_nonneg (b * star d - a * star c), norm_nonneg (a * d - b * c)]
  have hsum : 0 < U + V := by
    have hv : 0 ≤ V := norm_nonneg _
    linarith
  have hden : (U + V) ^ 2 ≤ D := young_denominator U V s hs
  have hf : N / (U + V) ≤ f := MobiusDisk.rationalized_lower_bound a b c d η hE hN hη
  have hfN : N ≤ f * (U + V) := (div_le_iff₀ hsum).mp hf
  have hsq : N ^ 2 ≤ f ^ 2 * (U + V) ^ 2 := by
    have := pow_le_pow_left₀ hN.le hfN 2
    simpa only [mul_pow] using this
  have hfden : f ^ 2 * (U + V) ^ 2 ≤ f ^ 2 * D :=
    mul_le_mul_of_nonneg_left hden (sq_nonneg _)
  have hD : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hsum) hden
  have hh : L * D ≤ f ^ 2 * D := le_trans hL (le_trans hsq hfden)
  exact (mul_le_mul_iff_left₀ hD).mp hh

#print axioms tensor_ratio
#print axioms mobius_certificate

end
end Gebendorfer.RadenkovicGutman.Bernstein
