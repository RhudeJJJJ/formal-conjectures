/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The actual reciprocal-coordinate coefficients, their disk parameter and
the concrete coefficientwise certificate interface for the RG quotient.
-/
import Proofs.RadenkovicGutmanFocus

namespace Gebendorfer.RadenkovicGutman.Focus

noncomputable section

def a (d P Q : ℝ) : ℂ := (d : ℂ) * A P Q
def b (d y P Q : ℝ) : ℂ := (2 * y : ℝ) * (A P Q * g d y + N₀ y P Q)
def c (d y P Q : ℝ) : ℂ := (d : ℂ) * B y P Q
def e (d y P Q : ℝ) : ℂ := (2 * y : ℝ) * (B y P Q * g d y + D₀ y P Q)

theorem scaled_separation_general (a b center : ℂ) (d y : ℝ) (hy : 0 < y)
    (h : 0 < Complex.normSq (a * center + b) - r d y ^ 2 * Complex.normSq a) :
    0 < Complex.normSq ((2 * y : ℝ) * (a * center + b)) -
      Complex.normSq ((d : ℂ) * a) := by
  have hfactor : Complex.normSq ((2 * y : ℝ) * (a * center + b)) -
      Complex.normSq ((d : ℂ) * a) =
      (2 * y) ^ 2 * (Complex.normSq (a * center + b) - r d y ^ 2 * Complex.normSq a) := by
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_ofReal]
    unfold r
    field_simp
  rw [hfactor]
  exact mul_pos (sq_pos_of_pos (by linarith)) h

theorem scaled_separation (d y P Q : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) :
    0 < Complex.normSq (e d y P Q) - Complex.normSq (c d y P Q) ∧
    0 < Complex.normSq (b d y P Q) - Complex.normSq (a d P Q) := by
  have hs := concrete_separation d y P Q hd hy hP hQ
  exact ⟨scaled_separation_general _ _ _ d y hy hs.1,
    scaled_separation_general _ _ _ d y hy hs.2⟩

theorem disk_parameter (d y : ℝ) (hd : 0 < d) (hy : 0 < y) (ζ : ℂ)
    (hζ : ‖ζ - g d y‖ ≤ r d y) :
    ‖(ζ - g d y) / (r d y : ℂ)‖ ≤ 1 ∧
      ζ = g d y + (r d y : ℂ) * ((ζ - g d y) / (r d y : ℂ)) := by
  have hr : 0 < r d y := div_pos hd (by linarith)
  constructor
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (div_le_one hr).mpr hζ
  · field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
    ring

theorem scaled_quotient (d y P Q : ℝ) (hd : 0 < d) (hy : 0 < y)
    (ζ : ℂ) :
    let η := (ζ - g d y) / (r d y : ℂ)
    quotient y P Q ζ = (a d P Q * η + b d y P Q) /
      (c d y P Q * η + e d y P Q) := by
  dsimp only
  have hr : r d y ≠ 0 := (div_pos hd (show 0 < 2 * y by linarith)).ne'
  have hrc : (r d y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hdc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hf (A N : ℂ) : (d : ℂ) * A * ((ζ - g d y) / (r d y : ℂ)) +
      (2 * y : ℝ) * (A * g d y + N) = (2 * y : ℝ) * (A * ζ + N) := by
    unfold r
    push_cast
    field_simp [hdc, hyc]
    ring
  unfold quotient a b c e
  rw [hf, hf, mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr (show 2 * y ≠ 0 by linarith))]

/-- All geometric premises are discharged for the concrete coefficient family.
Only the exact coefficient/integral work remains to supply hL. -/
theorem concrete_certificate (d y P Q : ℝ) (hd : 0 < d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) (ζ : ℂ) (hζ : ‖ζ - g d y‖ ≤ r d y)
    (s L : ℝ) (hs : 0 < s)
    (hL : L * ((1 + s) * ‖b d y P Q * star (e d y P Q) -
          a d P Q * star (c d y P Q)‖ ^ 2 +
        (1 + 1 / s) * ‖a d P Q * e d y P Q - b d y P Q * c d y P Q‖ ^ 2) ≤
      (Complex.normSq (b d y P Q) - Complex.normSq (a d P Q)) ^ 2) :
    L ≤ ‖quotient y P Q ζ‖ ^ 2 := by
  have hsep := scaled_separation d y P Q hd.le hy hP hQ
  rw [scaled_quotient d y P Q hd hy ζ]
  exact Bernstein.mobius_certificate _ _ _ _ _ hsep.1 hsep.2
    (disk_parameter d y hd hy ζ hζ).1 s L hs hL

#print axioms scaled_separation
#print axioms scaled_quotient
#print axioms concrete_certificate

theorem denominator_nonzero (d y P Q : ℝ) (hd : 0 < d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) (ζ : ℂ) (hζ : ‖ζ - g d y‖ ≤ r d y) :
    B y P Q * ζ + D₀ y P Q ≠ 0 := by
  have hsep := scaled_separation d y P Q hd.le hy hP hQ
  let η := (ζ - g d y) / (r d y : ℂ)
  have hn := MobiusDisk.denominator_ne_zero (c d y P Q) (e d y P Q) η
    hsep.1 (disk_parameter d y hd hy ζ hζ).1
  have hdc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have he : c d y P Q * η + e d y P Q =
      (2 * y : ℝ) * (B y P Q * ζ + D₀ y P Q) := by
    unfold c e η r
    push_cast
    field_simp [hdc, hyc]
    ring
  intro hz
  apply hn
  rw [he, hz, mul_zero]

#print axioms denominator_nonzero

end
end Gebendorfer.RadenkovicGutman.Focus
