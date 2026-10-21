/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmClasses
namespace Gebendorfer.RadenkovicGutman.ArmRationalForm
open ArmClasses PathEnclosure
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def denominator (c : Fin 5) (y : ℝ) : ℝ :=
  if c.val=0 then 1 else if c.val=1 then y else if c.val=2 then y^2+1
  else if c.val=3 then y^3+2*y
  else y*(y^4+3*y^2+1)*(y^4+4*y^2+3)

def numerator (c : Fin 5) (y t : ℝ) : ℝ :=
  if c.val=0 then y else if c.val=1 then y^2+1 else if c.val=2 then y^3+2*y
  else if c.val=3 then y^4+3*y^2+1
  else y^2*(y^4+3*y^2+1)*(y^4+4*y^2+3)+(y^4+2*y^2)*(y^4+4*y^2+3)+t

theorem denominator_positive (c : Fin 5) (y : ℝ) (hy : 0 < y) :
    0 < denominator c y := by
  fin_cases c
  all_goals norm_num [denominator]
  all_goals positivity

/-- Exact rational forms for the same five physical arm classes. -/
theorem parameter_identity (c : Fin 5) (y t : ℝ) (hy : 0 < y) :
    parameter y c t=numerator c y t/denominator c y := by
  have hy2 : 0 < y^2 := sq_pos_of_pos hy
  fin_cases c
  all_goals norm_num [parameter,rho,arm,numerator,denominator,lower,upper]
  all_goals field_simp
  all_goals ring

theorem parameter_enclosure (c : Fin 5) (y t : ℝ) (hy : 0 < y)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ a ∈ Set.Icc (0 : ℝ) 1, parameter y c t=y+a/y := by
  by_cases hc : c.val < 4
  · refine ⟨arm y c.val,⟨arm_nonneg y c.val,arm_le_one y hy c.val⟩,?_⟩
    simp only [parameter,if_pos hc,rho]
  · let a := lower y+t*(upper y-lower y)
    have hl : 0 ≤ lower y := by unfold lower; positivity
    have hw : 0 ≤ upper y-lower y := (long_width_pos y hy).le
    have hu : upper y ≤ 1 := by
      unfold upper
      apply (div_le_one (by positivity)).mpr
      nlinarith [sq_nonneg y]
    have ha0 : 0 ≤ a := add_nonneg hl (mul_nonneg ht.1 hw)
    have ha1 : a ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right ht.2 hw
      dsimp [a]
      linarith
    exact ⟨a,⟨ha0,ha1⟩,by simp only [parameter,if_neg hc,a]⟩

#print axioms denominator_positive
#print axioms parameter_identity
#print axioms parameter_enclosure
end
end Gebendorfer.RadenkovicGutman.ArmRationalForm
