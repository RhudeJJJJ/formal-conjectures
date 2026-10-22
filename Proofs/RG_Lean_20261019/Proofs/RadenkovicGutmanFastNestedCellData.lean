/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastNestedClassBoxes

namespace Gebendorfer.RadenkovicGutman.FastNestedCellData
open NestedArithmetic
set_option maxHeartbeats 0

structure Cell where
  reciprocal : Bool
  young : ℚ
  squareLower : ℚ
  payment : ℚ
  logarithmK : ℕ
  logarithmN : ℕ
  poly : NestedHorner.Poly 3
  affine : NestedHorner.Poly 3
  degrees : Fin 3 → ℕ
  left : Fin 3 → ℚ
  width : Fin 3 → ℚ

def program (d : ℚ) (c₁ c₂ : Fin 5) (c : Cell) : Expr 3 :=
  if c.reciprocal=true then
    (NestedReciprocal.homogenize (NestedClassCell.gap d c₁ c₂ c.young c.squareLower)).2
  else NestedClassCell.gap d c₁ c₂ c.young c.squareLower

def accepts (d : ℚ) (c₁ c₂ : Fin 5) (c : Cell) : Bool :=
  decide (0 < c.young ∧ (∀ i, 0 < c.width i) ∧
    NestedArithmetic.accepts (program d c₁ c₂ c) c.poly=true ∧
    NestedAffine.check 3 c.poly c.affine c.left c.width=true ∧
    NestedHorner.positiveCheck 3 c.degrees c.affine=true ∧
    RationalLog.accepts c.squareLower c.payment c.logarithmK c.logarithmN=true)

noncomputable section
def ordinate (c : Cell) (z : Fin 3 → ℝ) : ℝ :=
  if c.reciprocal=true then 1/z 0 else z 0

/-- A record checks a whole parameter box, including reciprocal cells.
The ordinate transformation and the same class pair remain in the conclusion. -/
theorem accepts_sound (d : ℚ) (c₁ c₂ : Fin 5) (c : Cell)
    (h : accepts d c₁ c₂ c=true) (hd : 0 < (d : ℝ))
    (z : Fin 3 → ℝ) (hz : FastNestedClassBoxes.InBox c.left c.width z)
    (hu : 0 < z 0) (h₁ : z 1 ∈ Set.Icc (0 : ℝ) 1) (h₂ : z 2 ∈ Set.Icc (0 : ℝ) 1)
    (ζ : ℂ) (hζ : ‖ζ-Focus.g d (ordinate c z)‖ ≤ Focus.r d (ordinate c z)) :
    (c.payment : ℝ) ≤ Real.log ‖Focus.quotient (ordinate c z)
      (ArmClasses.parameter (ordinate c z) c₁ (z 1))
      (ArmClasses.parameter (ordinate c z) c₂ (z 2)) ζ‖ := by
  obtain ⟨hs,hw,hp,ha,hpositive,hl⟩ := of_decide_eq_true h
  by_cases hc : c.reciprocal=true
  · simp only [program,if_pos hc] at hp
    simp only [ordinate,if_pos hc] at hζ ⊢
    exact FastNestedClassBoxes.reciprocal_logarithm_lower d c₁ c₂ c.young c.squareLower c.payment
      c.logarithmK c.logarithmN c.poly c.affine c.degrees c.left c.width hw
      hp ha hpositive hl hd hs z hz hu h₁ h₂ ζ hζ
  · simp only [program,if_neg hc] at hp
    simp only [ordinate,if_neg hc] at hζ ⊢
    exact FastNestedClassBoxes.direct_logarithm_lower d c₁ c₂ c.young c.squareLower c.payment
      c.logarithmK c.logarithmN c.poly c.affine c.degrees c.left c.width hw
      hp ha hpositive hl hd hs z hz hu h₁ h₂ ζ hζ

#print axioms accepts_sound
end
end Gebendorfer.RadenkovicGutman.FastNestedCellData
