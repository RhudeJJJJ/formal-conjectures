/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedAffine
import Proofs.RadenkovicGutmanNestedClassCell
import Proofs.RadenkovicGutmanNestedReciprocal

namespace Gebendorfer.RadenkovicGutman.FastNestedClassBoxes
open NestedArithmetic NestedClassPolynomials
noncomputable section
set_option maxHeartbeats 0

def coordinate (l w : Fin 3 → ℚ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => (z i-(l i : ℝ))/(w i : ℝ)

def InBox (l w : Fin 3 → ℚ) (z : Fin 3 → ℝ) : Prop :=
  ∀ i, (l i : ℝ) ≤ z i ∧ z i ≤ (l i : ℝ)+(w i : ℝ)

theorem coordinate_mem (l w : Fin 3 → ℚ) (hw : ∀ i, 0 < w i)
    (z : Fin 3 → ℝ) (hz : InBox l w z) :
    ∀ i, coordinate l w z i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  have hwr : (0 : ℝ) < w i := by exact_mod_cast hw i
  constructor
  · exact div_nonneg (sub_nonneg.mpr (hz i).1) hwr.le
  · apply (div_le_one hwr).mpr
    linarith [(hz i).2]

theorem point_coordinate (l w : Fin 3 → ℚ) (hw : ∀ i, 0 < w i) (z : Fin 3 → ℝ) :
    NestedClassCell.point l w (coordinate l w z)=z := by
  funext i
  have hwr : (0 : ℝ) < w i := by exact_mod_cast hw i
  dsimp [NestedClassCell.point,coordinate]
  field_simp [hwr.ne']
  ring

theorem program_nonneg (e : Expr 3) (p a : NestedHorner.Poly 3)
    (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ) (hw : ∀ i, 0 < w i)
    (hprogram : accepts e p=true)
    (haffine : NestedAffine.check 3 p a l w=true)
    (hpositive : NestedHorner.positiveCheck 3 deg a=true)
    (z : Fin 3 → ℝ) (hz : InBox l w z) : 0 ≤ value e z := by
  let t := coordinate l w z
  have ht := coordinate_mem l w hw z hz
  have he := point_coordinate l w hw z
  have ha := NestedAffine.check_sound 3 p a l w haffine t
  change NestedHorner.eval a t=NestedHorner.eval p (NestedClassCell.point l w t) at ha
  rw [he] at ha
  calc
    0 ≤ NestedHorner.eval a t := NestedHorner.positiveCheck_sound 3 deg a hpositive t ht
    _ = NestedHorner.eval p z := ha
    _ = value e z := accepts_sound e p hprogram z

theorem logarithm_lower_of_gap (d : ℚ) (c₁ c₂ : Fin 5) (s L R : ℚ) (k n : ℕ)
    (hlog : RationalLog.accepts L R k n=true) (hd : 0 < (d : ℝ)) (hs : 0 < s)
    (z : Fin 3 → ℝ) (hy : 0 < z 0)
    (h₁ : z 1 ∈ Set.Icc (0 : ℝ) 1) (h₂ : z 2 ∈ Set.Icc (0 : ℝ) 1)
    (hgap : 0 ≤ value (NestedClassCell.gap d c₁ c₂ s L) z)
    (ζ : ℂ) (hζ : ‖ζ-Focus.g d (z 0)‖ ≤ Focus.r d (z 0)) :
    (R : ℝ) ≤ Real.log ‖Focus.quotient (z 0)
      (ArmClasses.parameter (z 0) c₁ (z 1)) (ArmClasses.parameter (z 0) c₂ (z 2)) ζ‖ := by
  have hcert : (L : ℝ)*((1+(s : ℝ))*value (programU d c₁ c₂) z+
      (1+1/(s : ℝ))*value (programV d c₁ c₂) z) ≤ value (programJ d c₁ c₂) z := by
    simp only [NestedClassCell.gap,value,Rat.cast_neg,Rat.cast_mul,Rat.cast_add,
      Rat.cast_div,Rat.cast_one] at hgap
    linarith
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  exact ClassCellCertificates.log_lower_of_square L R k n hlog _
    (NestedClassNorms.polynomial_certificate d c₁ c₂ z hd hy h₁ h₂ ζ hζ s L hsr hcert)

theorem direct_logarithm_lower (d : ℚ) (c₁ c₂ : Fin 5) (s L R : ℚ) (k n : ℕ)
    (p a : NestedHorner.Poly 3) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ)
    (hw : ∀ i, 0 < w i)
    (hprogram : accepts (NestedClassCell.gap d c₁ c₂ s L) p=true)
    (haffine : NestedAffine.check 3 p a l w=true)
    (hpositive : NestedHorner.positiveCheck 3 deg a=true)
    (hlog : RationalLog.accepts L R k n=true) (hd : 0 < (d : ℝ)) (hs : 0 < s)
    (z : Fin 3 → ℝ) (hz : InBox l w z) (hy : 0 < z 0)
    (h₁ : z 1 ∈ Set.Icc (0 : ℝ) 1) (h₂ : z 2 ∈ Set.Icc (0 : ℝ) 1)
    (ζ : ℂ) (hζ : ‖ζ-Focus.g d (z 0)‖ ≤ Focus.r d (z 0)) :
    (R : ℝ) ≤ Real.log ‖Focus.quotient (z 0)
      (ArmClasses.parameter (z 0) c₁ (z 1)) (ArmClasses.parameter (z 0) c₂ (z 2)) ζ‖ :=
  logarithm_lower_of_gap d c₁ c₂ s L R k n hlog hd hs z hy h₁ h₂
    (program_nonneg _ p a deg l w hw hprogram haffine hpositive z hz) ζ hζ

theorem reciprocal_logarithm_lower (d : ℚ) (c₁ c₂ : Fin 5) (s L R : ℚ) (k n : ℕ)
    (p a : NestedHorner.Poly 3) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ)
    (hw : ∀ i, 0 < w i)
    (hprogram : accepts (NestedReciprocal.homogenize (NestedClassCell.gap d c₁ c₂ s L)).2 p=true)
    (haffine : NestedAffine.check 3 p a l w=true)
    (hpositive : NestedHorner.positiveCheck 3 deg a=true)
    (hlog : RationalLog.accepts L R k n=true) (hd : 0 < (d : ℝ)) (hs : 0 < s)
    (z : Fin 3 → ℝ) (hz : InBox l w z) (hu : 0 < z 0)
    (h₁ : z 1 ∈ Set.Icc (0 : ℝ) 1) (h₂ : z 2 ∈ Set.Icc (0 : ℝ) 1)
    (ζ : ℂ) (hζ : ‖ζ-Focus.g d (1/z 0)‖ ≤ Focus.r d (1/z 0)) :
    (R : ℝ) ≤ Real.log ‖Focus.quotient (1/z 0)
      (ArmClasses.parameter (1/z 0) c₁ (z 1)) (ArmClasses.parameter (1/z 0) c₂ (z 2)) ζ‖ := by
  have hg := program_nonneg _ p a deg l w hw hprogram haffine hpositive z hz
  have hnonneg := NestedReciprocal.nonneg_of_homogenize _ z hu hg
  have h1 : NestedReciprocal.invert z 1=z 1 := NestedReciprocal.invert_other z 1 (by decide)
  have h2 : NestedReciprocal.invert z 2=z 2 := NestedReciprocal.invert_other z 2 (by decide)
  have hh := logarithm_lower_of_gap d c₁ c₂ s L R k n hlog hd hs (NestedReciprocal.invert z)
    (by rw [NestedReciprocal.invert_zero]; positivity)
    (by rw [h1]; exact h₁) (by rw [h2]; exact h₂) hnonneg ζ
    (by simpa only [NestedReciprocal.invert_zero] using hζ)
  simpa only [NestedReciprocal.invert_zero,h1,h2] using hh

#print axioms coordinate_mem
#print axioms point_coordinate
#print axioms program_nonneg
#print axioms logarithm_lower_of_gap
#print axioms direct_logarithm_lower
#print axioms reciprocal_logarithm_lower
end
end Gebendorfer.RadenkovicGutman.FastNestedClassBoxes
