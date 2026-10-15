/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Connection of the real invariant interval with actual path resolvents.
-/
import Proofs.RadenkovicGutmanPathResolvent
import Proofs.RadenkovicGutmanPathEnclosure

namespace Gebendorfer.RadenkovicGutman.PathEnclosure

open Gebendorfer.RadenkovicGutman.PathRecurrence
noncomputable section

def rho (y : ℝ) (n : ℕ) : ℝ := y + arm y n / y

theorem rho_pos (y : ℝ) (hy : 0 < y) (n : ℕ) : 0 < rho y n := by
  have h := arm_nonneg y n
  unfold rho
  positivity

theorem rho_succ (y : ℝ) (hy : 0 < y) (n : ℕ) :
    rho y (n + 1) = y + 1 / rho y n := by
  have ha := arm_nonneg y n
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  change y + (y ^ 2 / (y ^ 2 + arm y n)) / y = y + 1 / (y + arm y n / y)
  field_simp

theorem tau_step (z h : ℂ) (hn : z - 1 - z * h ≠ 0) :
    z * (1 - (1 - h) / (z - 1 - z * h)) - 1 =
      z - 2 - 1 / (z * (1 - h) - 1) := by
  have he : z * (1 - h) - 1 = z - 1 - z * h := by ring
  rw [he]
  field_simp
  ring

/-- The complex path endpoint resolvent equals the real continued fraction. -/
theorem path_resolvent_real (y : ℝ) (hy : 0 < y) (n : ℕ) :
    let z : ℂ := 2 + Complex.I * y
    z * (1 - resolventQuotient z (n + 1)) - 1 = Complex.I * (rho y n : ℂ) := by
  let z : ℂ := 2 + Complex.I * y
  have hz : z.im ≠ 0 := by simpa [z] using hy.ne'
  have hz0 : z ≠ 0 := by intro h; apply hz; simp [h]
  change z * (1 - resolventQuotient z (n + 1)) - 1 = Complex.I * (rho y n : ℂ)
  induction n with
  | zero =>
    simp only [resolventQuotient, num_succ, den_succ, num_zero, den_zero,
      rho, arm]
    simp
    field_simp
    dsimp [z]
    ring
  | succ n ih =>
    have hr : (rho y n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos y hy n).ne'
    have hd : z - 1 - z * resolventQuotient z (n + 1) ≠ 0 := by
      have he : z - 1 - z * resolventQuotient z (n + 1) = Complex.I * (rho y n : ℂ) := by
        linear_combination ih
      rw [he]
      exact mul_ne_zero Complex.I_ne_zero hr
    rw [resolventQuotient_succ z (n + 1) (den_ne_zero_of_im_ne_zero z hz n),
      tau_step z _ hd, ih, rho_succ y hy n]
    push_cast
    have hzz : z - 2 = Complex.I * (y : ℂ) := by dsimp [z]; ring
    rw [hzz]
    field_simp
    simp only [Complex.I_sq]
    ring

/-- All long actual path resolvents satisfy the manuscript's invariant interval. -/
theorem all_long_path_resolvents (y : ℝ) (hy : 0 < y) (n : ℕ) :
    let z : ℂ := 2 + Complex.I * y
    let h := (pathMatrix z (n + 5))⁻¹ 0 0
    ∃ a : ℝ, lower y ≤ a ∧ a ≤ upper y ∧
      z * (1 - h) - 1 = Complex.I * ((y + a / y : ℝ) : ℂ) := by
  dsimp only
  refine ⟨arm y (n + 4), (all_long_arms y hy n).1, (all_long_arms y hy n).2, ?_⟩
  rw [pathMatrix_inv_endpoint]
  exact path_resolvent_real y hy (n + 4)

#print axioms path_resolvent_real
#print axioms all_long_path_resolvents

end
end Gebendorfer.RadenkovicGutman.PathEnclosure
