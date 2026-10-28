module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-! # Exact radical comparison for the H5 witness

The rational separating bounds are from the linked manuscript's order-five
comparison. No approximate numerical eigenvalue is used.
-/

@[expose] public section
namespace JiaSong.Certificate

theorem radical_comparison :
    4 - Real.sqrt 41 / 2 < (5 / 4 : ℝ) + (4 - Real.sqrt 24) / 2 := by
  have h41 : Real.sqrt 41 ^ 2 = 41 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h41pos := Real.sqrt_nonneg (41 : ℝ)
  have h6pos := Real.sqrt_nonneg (6 : ℝ)
  have h41lower : (32 / 5 : ℝ) < Real.sqrt 41 := by nlinarith
  have h6upper : Real.sqrt 6 < (49 / 20 : ℝ) := by nlinarith
  have h24 : Real.sqrt (24 : ℝ) = 2 * Real.sqrt 6 := by
    rw [show (24 : ℝ) = 4 * 6 by norm_num, Real.sqrt_mul (by norm_num)]
    rw [show (4 : ℝ) = (2 : ℝ)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h24]
  linarith

end JiaSong.Certificate
