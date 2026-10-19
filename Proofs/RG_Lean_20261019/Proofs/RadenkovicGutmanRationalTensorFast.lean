/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Fast exact binomial evaluation for rational Bernstein certificates.
The computational checker is proved equivalent to the original checker.
-/
import Proofs.RadenkovicGutmanRationalTensorPolynomial

namespace Gebendorfer.RadenkovicGutman.RationalTensorPolynomial
open Finset

def fastFactor {n : ℕ} (d e j : Exponent n) : ℚ :=
  ∏ i, if e i ≤ j i then (Nat.fast_choose (d i - e i) (j i - e i) : ℚ) else 0

def fastCoefficient {n : ℕ} (d j : Exponent n) : Poly n → ℚ
  | [] => 0
  | t :: p => t.1 * fastFactor d t.2 j + fastCoefficient d j p

theorem fastFactor_eq {n : ℕ} (d e j : Exponent n) : fastFactor d e j = factor d e j := by
  simp only [fastFactor, factor, ← Nat.choose_eq_fast_choose]

theorem fastCoefficient_eq {n : ℕ} (d j : Exponent n) (p : Poly n) :
    fastCoefficient d j p = coefficient d j p := by
  induction p with
  | nil => rfl
  | cons t p ih => simp only [fastCoefficient, coefficient, fastFactor_eq, ih]

def acceptsFast {n : ℕ} (d : Exponent n) (p : Poly n) : Bool :=
  decide (bounded d p ∧ ∀ j : (∀ i, Fin (d i + 1)),
    0 ≤ fastCoefficient d (fun i => (j i : ℕ)) p)

theorem acceptsFast_sound {n : ℕ} (d : Exponent n) (p : Poly n)
    (hc : acceptsFast d p = true) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ evaluate x p := by
  have h : bounded d p ∧ ∀ j : (∀ i, Fin (d i + 1)),
      0 ≤ fastCoefficient d (fun i => (j i : ℕ)) p := of_decide_eq_true hc
  have hold : accepts d p = true := by
    apply decide_eq_true
    simpa only [fastCoefficient_eq] using h
  exact accepts_sound d p hold x hx

#print axioms fastFactor_eq
#print axioms fastCoefficient_eq
#print axioms acceptsFast_sound
end Gebendorfer.RadenkovicGutman.RationalTensorPolynomial
