/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The univariate expansion proof is adapted from LeanCert contributors,
Apache 2.0, commit 621a43d7cf21f87872392a01e874f2f1dbddc926.
Rational tensor Bernstein coefficients for the finite-degree integral cells.
Source: the compact integral certificates for pendant-path fusion,
September 2026, and the binomial expansion of monomials.
-/
import Proofs.RadenkovicGutmanTensorPolynomial

namespace Gebendorfer.RadenkovicGutman.RationalTensorPolynomial
open Finset
open scoped Classical

abbrev Exponent (n : ℕ) := Fin n → ℕ
abbrev Term (n : ℕ) := ℚ × Exponent n
abbrev Poly (n : ℕ) := List (Term n)

noncomputable def monomial {n : ℕ} (x : Fin n → ℝ) (e : Exponent n) : ℝ :=
  ∏ i, x i ^ e i

noncomputable def evaluate {n : ℕ} (x : Fin n → ℝ) : Poly n → ℝ
  | [] => 0
  | t :: p => t.1 * monomial x t.2 + evaluate x p

def bounded {n : ℕ} (d : Exponent n) (p : Poly n) : Prop :=
  ∀ t ∈ p, ∀ i, t.2 i ≤ d i

instance {n : ℕ} (d : Exponent n) (p : Poly n) : Decidable (bounded d p) :=
  inferInstanceAs (Decidable (∀ t ∈ p, ∀ i, t.2 i ≤ d i))

def factor {n : ℕ} (d e j : Exponent n) : ℚ :=
  ∏ i, if e i ≤ j i then (Nat.choose (d i - e i) (j i - e i) : ℚ) else 0

def coefficient {n : ℕ} (d j : Exponent n) : Poly n → ℚ
  | [] => 0
  | t :: p => t.1 * factor d t.2 j + coefficient d j p

noncomputable def weight {n : ℕ} (d j : Exponent n) (x : Fin n → ℝ) : ℝ :=
  ∏ i, x i ^ j i * (1 - x i) ^ (d i - j i)

theorem weight_nonneg {n : ℕ} (d j : Exponent n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ weight d j x := by
  exact Finset.prod_nonneg (fun i _ =>
    mul_nonneg (pow_nonneg (hx i).1 _) (pow_nonneg (sub_nonneg.mpr (hx i).2) _))

theorem monomial_expansion {n : ℕ} (d e : Exponent n) (he : ∀ i, e i ≤ d i)
    (x : Fin n → ℝ) :
    monomial x e = ∑ j : (∀ i, Fin (d i + 1)),
      (factor d e (fun i => (j i : ℕ)) : ℝ) *
        weight d (fun i => (j i : ℕ)) x := by
  have hi (i : Fin n) : x i ^ e i = ∑ j : Fin (d i + 1),
      ((if e i ≤ (j : ℕ) then
        (Nat.choose (d i - e i) ((j : ℕ) - e i) : ℚ) else 0 : ℚ) : ℝ) *
        (x i ^ (j : ℕ) * (1 - x i) ^ (d i - (j : ℕ))) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ((if e i ≤ j then (Nat.choose (d i - e i) (j - e i) : ℚ) else 0 : ℚ) : ℝ) *
        (x i ^ j * (1 - x i) ^ (d i - j))) (d i + 1)]
    simpa only [apply_ite, Rat.cast_natCast, Rat.cast_zero, mul_assoc,
      ite_mul, zero_mul] using
      TensorPolynomial.power_expansion (d i) (e i) (he i) (x i)
  unfold monomial
  simp_rw [hi]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [factor, weight, Rat.cast_prod]
  exact Finset.prod_mul_distrib

theorem representation {n : ℕ} (d : Exponent n) (p : Poly n) (hp : bounded d p)
    (x : Fin n → ℝ) :
    evaluate x p = ∑ j : (∀ i, Fin (d i + 1)),
      (coefficient d (fun i => (j i : ℕ)) p : ℝ) *
        weight d (fun i => (j i : ℕ)) x := by
  induction p with
  | nil => simp [evaluate, coefficient]
  | cons t p ih =>
    have ht : ∀ i, t.2 i ≤ d i := hp t (by simp)
    have hrest : bounded d p := fun u hu => hp u (by simp [hu])
    simp only [evaluate, coefficient, Rat.cast_add, Rat.cast_mul, add_mul,
      Finset.sum_add_distrib, ← ih hrest]
    rw [monomial_expansion d t.2 ht x, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

def accepts {n : ℕ} (d : Exponent n) (p : Poly n) : Bool :=
  decide (bounded d p ∧ ∀ j : (∀ i, Fin (d i + 1)),
    0 ≤ coefficient d (fun i => (j i : ℕ)) p)

theorem accepts_sound {n : ℕ} (d : Exponent n) (p : Poly n)
    (hc : accepts d p = true) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ evaluate x p := by
  have h : bounded d p ∧ ∀ j : (∀ i, Fin (d i + 1)),
      0 ≤ coefficient d (fun i => (j i : ℕ)) p := of_decide_eq_true hc
  rw [representation d p h.1 x]
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (by exact_mod_cast h.2 j) (weight_nonneg d _ x hx)

#print axioms monomial_expansion
#print axioms representation
#print axioms accepts_sound
end Gebendorfer.RadenkovicGutman.RationalTensorPolynomial
