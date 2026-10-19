/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The univariate expansion proof is adapted from LeanCert contributors,
Apache 2.0, commit 621a43d7cf21f87872392a01e874f2f1dbddc926.
Kernel-checkable tensor Bernstein coefficients for exact polynomial cells.
Source: the compact integral certificates for pendant-path fusion,
September 2026, and the binomial expansion of monomials.
-/
import Mathlib.Tactic

namespace Gebendorfer.RadenkovicGutman.TensorPolynomial
open Finset
open scoped Classical

abbrev Exponent (n : ℕ) := Fin n → ℕ
abbrev Term (n : ℕ) := ℤ × Exponent n
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

def factor {n : ℕ} (d e j : Exponent n) : ℤ :=
  ∏ i, if e i ≤ j i then (Nat.choose (d i - e i) (j i - e i) : ℤ) else 0

def coefficient {n : ℕ} (d j : Exponent n) : Poly n → ℤ
  | [] => 0
  | t :: p => t.1 * factor d t.2 j + coefficient d j p

noncomputable def weight {n : ℕ} (d j : Exponent n) (x : Fin n → ℝ) : ℝ :=
  ∏ i, x i ^ j i * (1 - x i) ^ (d i - j i)

theorem weight_nonneg {n : ℕ} (d j : Exponent n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ weight d j x := by
  exact Finset.prod_nonneg (fun i _ =>
    mul_nonneg (pow_nonneg (hx i).1 _) (pow_nonneg (sub_nonneg.mpr (hx i).2) _))

private theorem univariate_expansion (n j : ℕ) (hjn : j ≤ n) (t : ℝ) :
    t ^ j = (Finset.range (n + 1)).sum (fun k =>
      if j ≤ k then (Nat.choose (n - j) (k - j) : ℝ) * t ^ k * (1 - t) ^ (n - k)
      else 0) := by
  -- Step 1: t^j = t^j * (t + (1-t))^(n-j)
  have h1 : t + (1 - t) = (1 : ℝ) := by ring
  have hstart : t ^ j = t ^ j * (t + (1 - t)) ^ (n - j) := by
    rw [h1, one_pow, mul_one]
  rw [hstart]
  -- Step 2: expand (t + (1-t))^(n-j) via binomial theorem
  rw [add_pow t (1 - t) (n - j)]
  -- Goal: t^j * Σ_m C(n-j,m) * t^m * (1-t)^(n-j-m) = Σ_k if j≤k then ...
  rw [Finset.mul_sum]
  -- Step 3: reindex the sum. LHS sums over m ∈ range(n-j+1), RHS over k ∈ range(n+1)
  -- Let k = m + j, so m = k - j
  -- We split the RHS: terms with k < j are 0, terms with j ≤ k contribute
  -- First simplify: the RHS sum over k < j gives 0
  have hsplit : (Finset.range (n + 1)).sum (fun k =>
      if j ≤ k then (Nat.choose (n - j) (k - j) : ℝ) * t ^ k * (1 - t) ^ (n - k)
      else 0) =
    (Finset.range (n - j + 1)).sum (fun m =>
      (Nat.choose (n - j) m : ℝ) * t ^ (m + j) * (1 - t) ^ (n - j - m)) := by
    -- Reindex: k = m + j
    rw [show n + 1 = j + (n + 1 - j) from by omega]
    rw [Finset.sum_range_add]
    -- The first part (k < j) sums to 0
    have hfirst : (Finset.range j).sum (fun k =>
        if j ≤ k then (Nat.choose (n - j) (k - j) : ℝ) * t ^ k * (1 - t) ^ (n - k)
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      simp only [show ¬(j ≤ k) from by omega, ite_false]
    rw [hfirst, zero_add]
    -- Second part: ∑ m in range(n+1-j), f(m+j)
    -- f(m+j) = if j ≤ m+j then C(n-j, m+j-j) * t^(m+j) * (1-t)^(n-(m+j)) else 0
    --        = C(n-j, m) * t^(m+j) * (1-t)^(n-j-m)
    rw [show n + 1 - j = n - j + 1 from by omega]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_range] at hm
    have hjle : j ≤ j + m := Nat.le_add_right j m
    rw [if_pos hjle]
    have h1 : j + m - j = m := by omega
    have h2 : n - (j + m) = n - j - m := by omega
    rw [h1, h2]
    ring
  rw [hsplit]
  -- Now both sides sum over m ∈ range(n-j+1)
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  -- LHS: t^j * (t^m * (1-t)^(n-j-m) * C(n-j,m))
  -- RHS: C(n-j,m) * t^(m+j) * (1-t)^(n-j-m)
  rw [pow_add t m j]
  ring


theorem monomial_expansion {n : ℕ} (d e : Exponent n) (he : ∀ i, e i ≤ d i)
    (x : Fin n → ℝ) :
    monomial x e = ∑ j : (∀ i, Fin (d i + 1)),
      (factor d e (fun i => (j i : ℕ)) : ℝ) *
        weight d (fun i => (j i : ℕ)) x := by
  have hi (i : Fin n) : x i ^ e i = ∑ j : Fin (d i + 1),
      ((if e i ≤ (j : ℕ) then
        (Nat.choose (d i - e i) ((j : ℕ) - e i) : ℤ) else 0 : ℤ) : ℝ) *
        (x i ^ (j : ℕ) * (1 - x i) ^ (d i - (j : ℕ))) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ((if e i ≤ j then (Nat.choose (d i - e i) (j - e i) : ℤ) else 0 : ℤ) : ℝ) *
        (x i ^ j * (1 - x i) ^ (d i - j))) (d i + 1)]
    simpa only [Int.cast_ite, Int.cast_natCast, Int.cast_zero, mul_assoc,
      ite_mul, zero_mul] using
      univariate_expansion (d i) (e i) (he i) (x i)
  unfold monomial
  simp_rw [hi]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [factor, weight, Int.cast_prod]
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
    simp only [evaluate, coefficient, Int.cast_add, Int.cast_mul, add_mul,
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

theorem power_expansion (n j : ℕ) (hj : j ≤ n) (t : ℝ) :
    t ^ j = (Finset.range (n + 1)).sum (fun k =>
      if j ≤ k then (Nat.choose (n - j) (k - j) : ℝ) * t ^ k * (1 - t) ^ (n - k)
      else 0) := univariate_expansion n j hj t

#print axioms monomial_expansion
#print axioms representation
#print axioms accepts_sound
#print axioms power_expansion
end Gebendorfer.RadenkovicGutman.TensorPolynomial
