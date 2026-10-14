/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.

The exact all-length path recurrence and singleton-normalization identity
used by the RG reconstruction. The determinant/resolvent interpretation and
the analytic sign certificates remain separate proof obligations.
-/
import Mathlib.Tactic

namespace Gebendorfer.RadenkovicGutman.PathRecurrence

variable {R : Type*} [CommRing R]

/-- Numerator and denominator states, including the algebraic initial state. -/
def state (z : R) : ℕ → R × R
  | 0 => (-1, 0)
  | n + 1 => let s := state z n
             (s.2 - s.1, (z - 1) * s.2 - z * s.1)

def num (z : R) (n : ℕ) : R := (state z n).1
def den (z : R) (n : ℕ) : R := (state z n).2

@[simp] theorem num_zero (z : R) : num z 0 = -1 := rfl
@[simp] theorem den_zero (z : R) : den z 0 = 0 := rfl
@[simp] theorem num_succ (z : R) (n : ℕ) :
    num z (n + 1) = den z n - num z n := rfl
@[simp] theorem den_succ (z : R) (n : ℕ) :
    den z (n + 1) = (z - 1) * den z n - z * num z n := rfl

theorem initial_state (z : R) : num z 1 = 1 ∧ den z 1 = z := by
  simp

/-- The two coupled addition formulas; no division or nonzero premise. -/
theorem addition (z : R) (p q : ℕ) :
    den z (p + q) = den z p * den z q - num z p * den z q -
      num z q * den z p ∧
    z * num z (p + q) = den z p * den z q - z * num z p * num z q := by
  induction p with
  | zero => simp
  | succ p ih =>
    rcases ih with ⟨hb, ha⟩
    constructor
    · rw [Nat.succ_add, den_succ, hb, ha, den_succ, num_succ]
      ring
    · rw [Nat.succ_add, num_succ, mul_sub, hb, ha, den_succ, num_succ]
      ring

/-- The singleton-core cancellation is valid for every pair of arm lengths. -/
theorem singleton_normalization (z : R) (p q : ℕ) :
    z * ((den z p - num z p) * (den z q - num z q)) -
      (2 * den z p * den z q - num z p * den z q - num z q * den z p) =
    z * (den z (p + q) - num z (p + q)) - den z (p + q) := by
  rcases addition z p q with ⟨hb, ha⟩
  rw [hb]
  linear_combination ha

theorem characteristic_recurrence (z : R) (n : ℕ) :
    den z (n + 2) = (z - 2) * den z (n + 1) - den z n := by
  rw [show n + 2 = (n + 1) + 1 by omega, den_succ, num_succ, den_succ]
  ring

variable {K : Type*} [Field K]

def resolventQuotient (z : K) (n : ℕ) : K := num z n / den z n

/-- The endpoint rational recurrence from Lemma 2.3 of the RG manuscript. -/
theorem resolventQuotient_succ (z : K) (n : ℕ) (hb : den z n ≠ 0) :
    resolventQuotient z (n + 1) =
      (1 - resolventQuotient z n) / (z - 1 - z * resolventQuotient z n) := by
  unfold resolventQuotient
  rw [num_succ, den_succ]
  field_simp

#print axioms addition
#print axioms singleton_normalization
#print axioms characteristic_recurrence
#print axioms resolventQuotient_succ

end Gebendorfer.RadenkovicGutman.PathRecurrence
