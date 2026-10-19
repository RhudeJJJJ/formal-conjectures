/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The all-length real arm addition law and the concrete reciprocal quotient.
-/
import Proofs.RadenkovicGutmanScaledQuotient
import Proofs.RadenkovicGutmanArmBridge

namespace Gebendorfer.RadenkovicGutman.PathEnclosure

theorem rho_ge (y : ℝ) (hy : 0 < y) (n : ℕ) : y ≤ rho y n := by
  unfold rho
  have hn := arm_nonneg y n
  exact le_add_of_nonneg_right (div_nonneg hn hy.le)

theorem rho_addition (y : ℝ) (hy : 0 < y) (p q : ℕ) :
    rho y (p + q + 1) = (1 + rho y p * rho y q) / (rho y p + rho y q - y) := by
  have h0 : rho y 0 = y := by simp [rho, arm]
  induction p with
  | zero =>
    rw [zero_add, rho_succ y hy q, h0]
    have hq := (rho_pos y hy q).ne'
    rw [add_sub_cancel_left]
    field_simp
    ring
  | succ p ih =>
    rw [show p + 1 + q + 1 = (p + q + 1) + 1 by omega,
      rho_succ y hy (p + q + 1), ih, rho_succ y hy p]
    have hpp := rho_pos y hy p
    have hp := hpp.ne'
    have hq := rho_pos y hy q
    have hprod : 1 + rho y p * rho y q ≠ 0 := by positivity
    have hsum : rho y p + rho y q - y ≠ 0 := by
      have h := rho_ge y hy p
      linarith
    have he : (y + 1 / rho y p) + rho y q - y =
        (1 + rho y p * rho y q) / rho y p := by field_simp; ring
    rw [he]
    field_simp [hprod, hp]
    ring

#print axioms rho_addition

end Gebendorfer.RadenkovicGutman.PathEnclosure

namespace Gebendorfer.RadenkovicGutman.Focus

noncomputable section

def m (y P Q : ℝ) : ℝ := (1 + P * Q) / (P + Q - y)

/-- The exact normalized endpoint formula equals the concrete Mobius quotient. -/
theorem normalized_mobius (y P Q : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q)
    (ζ : ℂ) (hζ : ζ ≠ 0) :
    let hp : ℂ := 1 - (1 + Complex.I * (P : ℂ)) / z y
    let hq : ℂ := 1 - (1 + Complex.I * (Q : ℂ)) / z y
    let hr : ℂ := 1 - (1 + Complex.I * (m y P Q : ℂ)) / z y
    let k := ζ⁻¹
    let A₀ := (1 - hp) * (1 - hq)
    let B₀ := 2 - hp - hq
    let C₀ := 1 - hr
    ((A₀ - B₀ * k) / (A₀ - B₀ * (1 / z y))) *
      ((C₀ - 1 / z y) / (C₀ - k)) = quotient y P Q ζ := by
  dsimp only
  have hp : 0 < P := lt_of_lt_of_le hy hP
  have hq : 0 < Q := lt_of_lt_of_le hy hQ
  have hsum : 0 < P + Q - y := by linarith
  have hprod : 0 < 1 + P * Q := by positivity
  have hz : z y ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [z] at hi
    linarith
  have hs : ((P + Q - y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsum.ne'
  have hpc : ((1 + P * Q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hprod.ne'
  push_cast at hs hpc
  have hB0 : (2 - (1 - (1 + Complex.I * (P : ℂ)) / z y) -
      (1 - (1 + Complex.I * (Q : ℂ)) / z y)) =
      (2 + Complex.I * ((P : ℂ) + (Q : ℂ))) / z y := by ring
  rw [hB0]
  simp only [sub_sub_cancel]
  have hA : ((1 + Complex.I * (P : ℂ)) / z y) *
      ((1 + Complex.I * (Q : ℂ)) / z y) = -(A P Q) / z y ^ 2 := by
    unfold A
    push_cast
    field_simp [hz]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  rw [hA]
  have hNorm : -(A P Q) / z y ^ 2 -
      ((2 + Complex.I * ((P : ℂ) + (Q : ℂ))) / z y) * (1 / z y) =
      -((1 + (P : ℂ) * (Q : ℂ))) / z y ^ 2 := by
    unfold A
    push_cast
    field_simp [hz]
    ring
  rw [hNorm]
  have hNum : -(A P Q) / z y ^ 2 -
      ((2 + Complex.I * ((P : ℂ) + (Q : ℂ))) / z y) * ζ⁻¹ =
      -(A P Q * ζ + N₀ y P Q) / (z y ^ 2 * ζ) := by
    unfold N₀
    push_cast
    field_simp [hz, hζ]
    ring
  rw [hNum]
  have hC : (1 + Complex.I * (m y P Q : ℂ)) / z y - ζ⁻¹ =
      Complex.I * (B y P Q * ζ + D₀ y P Q) /
        (((P : ℂ) + (Q : ℂ) - (y : ℂ)) * z y * ζ) := by
    unfold B D₀ m
    push_cast
    field_simp [hz, hζ, hs]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  rw [hC]
  have hC0 : (1 + Complex.I * (m y P Q : ℂ)) / z y - 1 / z y =
      Complex.I * (m y P Q : ℂ) / z y := by ring
  rw [hC0]
  unfold quotient m
  push_cast
  field_simp [hz, hζ, hs, hpc, Complex.I_ne_zero]

#print axioms normalized_mobius

end
end Gebendorfer.RadenkovicGutman.Focus
