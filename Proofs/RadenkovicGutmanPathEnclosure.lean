/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The invariant interval for the real continued-fraction arm recurrence.
The index n represents manuscript arm length n+1. The connection of this
real recurrence to the complex graph resolvent is a separate bridge.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Gebendorfer.RadenkovicGutman.PathEnclosure

noncomputable section

def arm (y : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => y ^ 2 / (y ^ 2 + arm y n)

def lower (y : ℝ) : ℝ := (y ^ 4 + 2 * y ^ 2) / (y ^ 4 + 3 * y ^ 2 + 1)
def upper (y : ℝ) : ℝ := (y ^ 4 + 3 * y ^ 2 + 1) / (y ^ 4 + 4 * y ^ 2 + 3)

theorem arm_nonneg (y : ℝ) (n : ℕ) : 0 ≤ arm y n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact div_nonneg (sq_nonneg y) (add_nonneg (sq_nonneg y) ih)

theorem arm_le_one (y : ℝ) (hy : 0 < y) (n : ℕ) : arm y n ≤ 1 := by
  cases n with
  | zero => norm_num [arm]
  | succ n =>
    have ha := arm_nonneg y n
    have hp : 0 < y ^ 2 := sq_pos_of_pos hy
    exact (div_le_one (by positivity)).mpr (by linarith)

theorem arm_four (y : ℝ) (hy : 0 < y) : arm y 4 = lower y := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  simp only [arm]
  unfold lower
  field_simp
  ring

theorem interval_width (y : ℝ) (hy : 0 < y) :
    upper y - lower y =
      1 / ((y ^ 4 + 3 * y ^ 2 + 1) * (y ^ 4 + 4 * y ^ 2 + 3)) := by
  have h4 : 0 ≤ y ^ 4 := by positivity
  have h2 : 0 ≤ y ^ 2 := sq_nonneg y
  unfold upper lower
  field_simp
  ring

theorem step_lower (y : ℝ) (hy : 0 < y) :
    y ^ 2 / (y ^ 2 + lower y) = upper y := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  unfold lower upper
  field_simp
  ring

theorem step_upper_ge_lower (y : ℝ) (hy : 0 < y) :
    lower y ≤ y ^ 2 / (y ^ 2 + upper y) := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  have h4 : 0 ≤ y ^ 4 := by positivity
  unfold lower upper
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  field_simp
  nlinarith [sq_nonneg (y ^ 2), sq_nonneg (y ^ 3)]

/-- Every arm length at least five lies in this single invariant interval. -/
theorem all_long_arms (y : ℝ) (hy : 0 < y) (n : ℕ) :
    lower y ≤ arm y (n + 4) ∧ arm y (n + 4) ≤ upper y := by
  have hl : 0 ≤ lower y := by unfold lower; positivity
  have hu : lower y ≤ upper y := by
    have h := interval_width y hy
    have hp : 0 < 1 / ((y ^ 4 + 3 * y ^ 2 + 1) * (y ^ 4 + 4 * y ^ 2 + 3)) := by
      positivity
    linarith
  induction n with
  | zero => simpa only [zero_add, arm_four y hy] using And.intro le_rfl hu
  | succ n ih =>
    change lower y ≤ y ^ 2 / (y ^ 2 + arm y (n + 4)) ∧
      y ^ 2 / (y ^ 2 + arm y (n + 4)) ≤ upper y
    have ha : 0 ≤ arm y (n + 4) := arm_nonneg y _
    have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
    constructor
    · exact (step_upper_ge_lower y hy).trans
        (div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) (by linarith [ih.2]))
    · rw [← step_lower y hy]
      exact div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) (by linarith [ih.1])

#print axioms all_long_arms

end
end Gebendorfer.RadenkovicGutman.PathEnclosure
