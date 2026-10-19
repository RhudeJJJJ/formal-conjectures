/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Exact rational logarithm certificates with power-of-two range reduction.
Source: the atanh series bounds in Mathlib.Analysis.SpecialFunctions.Log.Deriv.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Gebendorfer.RadenkovicGutman.RationalLog

def seriesPart (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1)

def error (x : ℚ) (n : ℕ) : ℚ := x ^ (2 * n + 1) / (1 - x ^ 2)

def accepts (L R : ℚ) (k n : ℕ) : Bool :=
  let v := 2 ^ k * L
  decide (0 < L ∧ 1 ≤ v ∧
    R ≤ seriesPart ((v - 1) / (v + 1)) n - k * (seriesPart (1 / 3) n + error (1 / 3) n))

theorem seriesPart_cast (x : ℚ) (n : ℕ) : (seriesPart x n : ℝ) =
    ∑ i ∈ Finset.range n, (x : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
  simp [seriesPart]

theorem sound (L R : ℚ) (k n : ℕ) (hc : accepts L R k n = true) :
    (R : ℝ) ≤ Real.log (L : ℝ) / 2 := by
  obtain ⟨hL, hv, hR⟩ := of_decide_eq_true hc
  let v : ℚ := 2 ^ k * L
  let u : ℚ := (v - 1) / (v + 1)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hv1 : (1 : ℝ) ≤ v := by
    change (1 : ℝ) ≤ (2 ^ k * L : ℚ)
    exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith
  have hu0 : (0 : ℝ) ≤ u := by
    dsimp [u]
    push_cast
    exact div_nonneg (by linarith) (by linarith)
  have hu1 : (u : ℝ) < 1 := by
    dsimp [u]
    push_cast
    apply (div_lt_one (by linarith : (0 : ℝ) < v + 1)).mpr
    linarith
  have huEq : (1 + (u : ℝ)) / (1 - (u : ℝ)) = v := by
    dsimp [u]
    push_cast
    field_simp
    ring
  have hs := Real.sum_range_le_log_div hu0 hu1 n
  rw [huEq, ← seriesPart_cast] at hs
  have ht := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1) n
  have htEq : (1 + (1 / 3 : ℝ)) / (1 - 1 / 3) = 2 := by norm_num
  rw [htEq] at ht
  have ht' : Real.log 2 / 2 ≤ (seriesPart (1 / 3) n + error (1 / 3) n : ℚ) := by
    simpa [seriesPart_cast, error, div_eq_mul_inv, mul_comm] using ht
  have hvEq : Real.log (v : ℝ) = (k : ℝ) * Real.log 2 + Real.log (L : ℝ) := by
    dsimp [v]
    push_cast
    rw [Real.log_mul (by positivity) hL0.ne', Real.log_pow]
  have hR' : (R : ℝ) ≤ (seriesPart u n : ℝ) -
      k * ((seriesPart (1 / 3) n + error (1 / 3) n : ℚ) : ℝ) := by
    dsimp [u, v]
    exact_mod_cast hR
  have hpay := mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  rw [hvEq] at hs
  linarith only [hs, hR', hpay]

#print axioms sound
end Gebendorfer.RadenkovicGutman.RationalLog
