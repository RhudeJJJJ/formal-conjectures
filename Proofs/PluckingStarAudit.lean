/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.PluckingStarProof

namespace PluckingStarAudit

/-- Independent operational recurrence, with right-to-left leaf indices. -/
noncomputable def starPolynomial : (n : ℕ) → (Fin n → ℕ) → Polynomial ℤ
  | 0, _ => 1
  | n+1, f => ∑ i : Fin (n+1), if f i = 1 then
      Polynomial.X ^ i.val * starPolynomial n (fun k => max 1 (f (i.succAbove k)-1)) else 0

def IsUnimodal (p : Polynomial ℤ) : Prop :=
  ∃ t : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ t → p.coeff i ≤ p.coeff j) ∧
    (∀ i j : ℕ, t ≤ i → i ≤ j → p.coeff j ≤ p.coeff i)

theorem starPolynomial_eq (n : ℕ) (f : Fin n → ℕ) :
    starPolynomial n f = PluckingStarProof.pluckPolynomial n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∑ i : Fin (n+1), if f i = 1 then _ else 0) =
      ∑ i : Fin (n+1), if f i = 1 then _ else 0
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    · rw [ih]
    · rfl

/-- Independently restated exact repository target, without a placeholder import. -/
theorem exact_statement : ∀ n : ℕ, ∀ f : Fin n → ℕ,
    (∀ i, f i = 1 ∨ f i = 2) → IsUnimodal (starPolynomial n f) := by
  intro n f hf
  rw [starPolynomial_eq]
  exact PluckingStarProof.conjecture4_1 n f hf

def outsideDelay : Fin 5 → ℕ := ![2,1,4,1,2]

/-- The known delay-four example has a genuine 5,4,5 valley; binary restriction matters. -/
theorem delay_four_counterexample :
    ¬ PluckingStarProof.PolynomialUnimodal (PluckingStarProof.pluckPolynomial 5 outsideDelay) := by
  have hc : PluckingStarProof.pluck 5 outsideDelay 4 = 5 ∧
      PluckingStarProof.pluck 5 outsideDelay 5 = 4 ∧
      PluckingStarProof.pluck 5 outsideDelay 6 = 5 := by decide
  intro hu
  obtain ⟨t,hl,hr⟩ := hu
  by_cases ht : t ≤ 5
  · have hh := hr 5 6 ht (by omega)
    simp only [PluckingStarProof.polynomial_coeff] at hh
    change PluckingStarProof.pluck 5 outsideDelay 6 ≤ PluckingStarProof.pluck 5 outsideDelay 5 at hh
    rw [hc.2.1,hc.2.2] at hh
    omega
  · have hh := hl 4 5 (by omega) (by omega)
    simp only [PluckingStarProof.polynomial_coeff] at hh
    change PluckingStarProof.pluck 5 outsideDelay 4 ≤ PluckingStarProof.pluck 5 outsideDelay 5 at hh
    rw [hc.1,hc.2.1] at hh
    omega

#print axioms PluckingStarProof.uniform_diff
#print axioms PluckingStarProof.unimodal_of_noReversal
#print axioms PluckingStarProof.first_window
#print axioms PluckingStarProof.uniform_unimodal
#print axioms PluckingStarProof.weighted_factorial
#print axioms PluckingStarProof.pluck_factorization
#print axioms PluckingStarProof.polynomial_coeff
#print axioms PluckingStarProof.polynomial_nonnegative
#print axioms PluckingStarProof.conjecture4_1
#print axioms starPolynomial_eq
#print axioms exact_statement
#print axioms delay_four_counterexample
end PluckingStarAudit

