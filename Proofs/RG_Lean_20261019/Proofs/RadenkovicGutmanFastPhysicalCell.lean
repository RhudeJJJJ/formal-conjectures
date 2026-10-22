/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastNestedCellData

namespace Gebendorfer.RadenkovicGutman.FastPhysicalCell
open FastNestedCellData
set_option maxHeartbeats 0

def shape (c : Cell) (a b : ℚ) : Bool :=
  decide (0 < a ∧ a < b ∧
    c.left 0=(if c.reciprocal=true then 1/b else a) ∧
    c.width 0=(if c.reciprocal=true then 1/a-1/b else b-a) ∧
    c.left 1=0 ∧ c.width 1=1 ∧ c.left 2=0 ∧ c.width 2=1)

noncomputable section

/-- The stored direct or reciprocal box covers exactly this physical
ordinate interval and the whole unit square of arm parameters. -/
theorem logarithm_lower (d : ℚ) (c₁ c₂ : Fin 5) (c : Cell) (a b : ℚ)
    (hcheck : FastNestedCellData.accepts d c₁ c₂ c=true) (hshape : shape c a b=true)
    (hd : 0 < (d : ℝ)) (y : ℝ) (hy : y ∈ Set.Icc (a : ℝ) (b : ℝ))
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ζ : ℂ) (hζ : ‖ζ-Focus.g d y‖ ≤ Focus.r d y) :
    (c.payment : ℝ) ≤ Real.log ‖Focus.quotient y
      (ArmClasses.parameter y c₁ s) (ArmClasses.parameter y c₂ t) ζ‖ := by
  obtain ⟨ha,hab,hl0,hw0,hl1,hw1,hl2,hw2⟩ := of_decide_eq_true hshape
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by
    have : (a : ℝ) < b := by exact_mod_cast hab
    exact har.trans this
  have hy0 : 0 < y := har.trans_le hy.1
  let v : ℝ := if c.reciprocal=true then 1/y else y
  let z : Fin 3 → ℝ := fun i => if i=0 then v else if i=1 then s else t
  have hz0 : z 0=v := by simp [z]
  have hz1 : z 1=s := by norm_num [z]
  have hz2 : z 2=t := by
    simp only [z,if_neg (by decide : (2 : Fin 3) ≠ 0),if_neg (by decide : (2 : Fin 3) ≠ 1)]
  have hbox0 : (c.left 0 : ℝ) ≤ z 0 ∧ z 0 ≤ (c.left 0 : ℝ)+(c.width 0 : ℝ) := by
    rw [hz0,hl0,hw0]
    by_cases hc : c.reciprocal=true
    · simp only [if_pos hc,v,Rat.cast_div,Rat.cast_one,Rat.cast_sub]
      have hlow : (1 : ℝ)/(b : ℝ) ≤ 1/y := by
        apply (div_le_div_iff₀ hbr hy0).mpr
        simpa only [one_mul] using hy.2
      have hhigh : (1 : ℝ)/y ≤ 1/(a : ℝ) := by
        apply (div_le_div_iff₀ hy0 har).mpr
        simpa only [one_mul] using hy.1
      constructor
      · exact hlow
      · linarith
    · simp only [if_neg hc,v,Rat.cast_sub]
      constructor
      · exact hy.1
      · linarith [hy.2]
  have hbox1 : (c.left 1 : ℝ) ≤ z 1 ∧ z 1 ≤ (c.left 1 : ℝ)+(c.width 1 : ℝ) := by
    simpa only [hl1,hw1,hz1,Rat.cast_zero,Rat.cast_one,zero_add,Set.mem_Icc] using hs
  have hbox2 : (c.left 2 : ℝ) ≤ z 2 ∧ z 2 ≤ (c.left 2 : ℝ)+(c.width 2 : ℝ) := by
    simpa only [hl2,hw2,hz2,Rat.cast_zero,Rat.cast_one,zero_add,Set.mem_Icc] using ht
  have hz : FastNestedClassBoxes.InBox c.left c.width z := by
    intro i
    fin_cases i
    · exact hbox0
    · exact hbox1
    · exact hbox2
  have hzu : 0 < z 0 := by
    rw [hz0]
    dsimp [v]
    split_ifs <;> positivity
  have he : ordinate c z=y := by
    simp only [ordinate,hz0,v]
    split_ifs <;> simp
  have hh := FastNestedCellData.accepts_sound d c₁ c₂ c hcheck hd z hz hzu
    (by rw [hz1]; exact hs) (by rw [hz2]; exact ht) ζ
    (by simpa only [he] using hζ)
  simpa only [he,hz1,hz2] using hh

#print axioms logarithm_lower
end
end Gebendorfer.RadenkovicGutman.FastPhysicalCell
