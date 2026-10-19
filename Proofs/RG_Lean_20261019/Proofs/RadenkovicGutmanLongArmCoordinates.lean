/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedHornerCells
namespace Gebendorfer.RadenkovicGutman.LongArmCoordinates
open Set
noncomputable section

def coordinate (inverse : Bool) (y : ℝ) : ℝ := if inverse then 1/(y^2) else y^2
def lower (inverse : Bool) (a b : ℝ) : ℝ := if inverse then 1/(b^2) else a^2
def upper (inverse : Bool) (a b : ℝ) : ℝ := if inverse then 1/(a^2) else b^2

theorem coordinate_mem (inverse : Bool) (a b y : ℝ) (ha : 0 < a) (hy : y ∈ Icc a b) :
    coordinate inverse y ∈ Icc (lower inverse a b) (upper inverse a b) := by
  have hy0 : 0 < y := ha.trans_le hy.1
  have hb0 : 0 < b := hy0.trans_le hy.2
  have hl : a^2 ≤ y^2 := (sq_le_sq₀ ha.le hy0.le).mpr hy.1
  have hu : y^2 ≤ b^2 := (sq_le_sq₀ hy0.le hb0.le).mpr hy.2
  cases inverse with
  | false => exact ⟨hl, hu⟩
  | true =>
    constructor
    · exact one_div_le_one_div_of_le (sq_pos_of_pos hy0) hu
    · exact one_div_le_one_div_of_le (sq_pos_of_pos ha) hl

#print axioms coordinate_mem
end
end Gebendorfer.RadenkovicGutman.LongArmCoordinates
