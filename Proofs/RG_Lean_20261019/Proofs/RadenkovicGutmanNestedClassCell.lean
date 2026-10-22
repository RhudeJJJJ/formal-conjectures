/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedClassNorms
import Proofs.RadenkovicGutmanClassCellCertificates

namespace Gebendorfer.RadenkovicGutman.NestedClassCell
open NestedArithmetic NestedClassPolynomials
set_option maxHeartbeats 0

/-- One polynomial inequality retains the same Young parameter for the
whole ordinate/arm cell. All arithmetic in the program is rational. -/
def gap (d : ℚ) (c₁ c₂ : Fin 5) (s L : ℚ) : Expr 3 :=
  .plus (programJ d c₁ c₂)
    (.plus (.scaled (-(L*(1+s))) (programU d c₁ c₂))
      (.scaled (-(L*(1+1/s))) (programV d c₁ c₂)))

noncomputable section
def point (l w : Fin 3 → ℚ) (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => (l i : ℝ)+(w i : ℝ)*t i

/-- Exact compilation, affine identity and Bernstein signs imply the
logarithmic bound throughout the cell for the actual arm classes. -/
theorem logarithm_lower (d : ℚ) (c₁ c₂ : Fin 5) (s L R : ℚ) (k n : ℕ)
    (p a : NestedHorner.Poly 3) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ)
    (hprogram : NestedArithmetic.accepts (gap d c₁ c₂ s L) p=true)
    (haffine : NestedHorner.affineCheck 3 deg p a l w=true)
    (hpositive : NestedHorner.positiveCheck 3 deg a=true)
    (hlog : RationalLog.accepts L R k n=true)
    (hd : 0 < (d : ℝ)) (hs : 0 < s)
    (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (hy : 0 < point l w t 0)
    (h₁ : point l w t 1 ∈ Set.Icc (0 : ℝ) 1)
    (h₂ : point l w t 2 ∈ Set.Icc (0 : ℝ) 1)
    (ζ : ℂ) (hζ : ‖ζ-Focus.g d (point l w t 0)‖ ≤ Focus.r d (point l w t 0)) :
    (R : ℝ) ≤ Real.log ‖Focus.quotient (point l w t 0)
      (ArmClasses.parameter (point l w t 0) c₁ (point l w t 1))
      (ArmClasses.parameter (point l w t 0) c₂ (point l w t 2)) ζ‖ := by
  have he := NestedArithmetic.accepts_sound _ _ hprogram (point l w t)
  have ha := NestedHorner.affineCheck_sound 3 deg p a l w haffine t
  have hp := NestedHorner.positiveCheck_sound 3 deg a hpositive t ht
  have hg : 0 ≤ value (gap d c₁ c₂ s L) (point l w t) := by
    calc
      0 ≤ NestedHorner.eval a t := hp
      _ = NestedHorner.eval p (point l w t) := ha
      _ = value (gap d c₁ c₂ s L) (point l w t) := he
  have hcert : (L : ℝ)*((1+(s : ℝ))*value (programU d c₁ c₂) (point l w t)+
      (1+1/(s : ℝ))*value (programV d c₁ c₂) (point l w t)) ≤
        value (programJ d c₁ c₂) (point l w t) := by
    simp only [gap,value,Rat.cast_neg,Rat.cast_mul,Rat.cast_add,Rat.cast_div,
      Rat.cast_one] at hg
    linarith
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hnorm := NestedClassNorms.polynomial_certificate d c₁ c₂ (point l w t)
    hd hy h₁ h₂ ζ hζ s L hsr hcert
  exact ClassCellCertificates.log_lower_of_square L R k n hlog _ hnorm

#print axioms logarithm_lower
end
end Gebendorfer.RadenkovicGutman.NestedClassCell
