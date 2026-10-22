/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedClassCell
namespace Gebendorfer.RadenkovicGutman.NestedCellControl
open NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def poly : Poly 3 := [[[0]],[[0]],[[(-14976/25)]],[[0]],[[(-9792/25)]],[[0]],[[(29208/25)]],[[0]],[[(28384/25)]],[[0]],[[(-776/25)]],[[0]],[[(-7248/25)]],[[0]],[[(-2336/25)]],[[0]],[[(-224/25)]]]
def affine : Poly 3 := [[[(4448/5)]],[[(50544/625)]],[[(1016/625)]],[[(-16529/781250)]],[[(-510191/312500000)]],[[(-122829/3125000000)]],[[(-1855619/3125000000000)]],[[(-252909/39062500000000)]],[[(-1686523/31250000000000000)]],[[(-552597/1562500000000000000)]],[[(-576409/312500000000000000000)]],[[(-29933/3906250000000000000000)]],[[(-39219/1562500000000000000000000)]],[[(-2471/39062500000000000000000000)]],[[(-913/7812500000000000000000000000)]],[[(-7/48828125000000000000000000000)]],[[(-7/78125000000000000000000000000000)]]]
def degrees : Fin 3 → ℕ := ![16,0,0]
def left : Fin 3 → ℚ := ![1,0,0]
def width : Fin 3 → ℚ := ![1/100,1,1]
theorem program_checked : NestedArithmetic.accepts
    (NestedClassCell.gap 1 0 0 (1/5) (13/10)) poly=true := by decide +kernel
theorem affine_checked : affineCheck 3 degrees poly affine left width=true := by decide +kernel
theorem signs_checked : positiveCheck 3 degrees affine=true := by decide +kernel
theorem logarithm_checked : RationalLog.accepts (13/10) (13/100) 0 12=true := by decide +kernel
noncomputable section
theorem actual_cell (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (ζ : ℂ) (hζ : ‖ζ-Focus.g 1 (NestedClassCell.point left width t 0)‖ ≤
      Focus.r 1 (NestedClassCell.point left width t 0)) :
    ((13/100 : ℚ) : ℝ) ≤ Real.log ‖Focus.quotient (NestedClassCell.point left width t 0)
      (ArmClasses.parameter (NestedClassCell.point left width t 0) 0 (t 1))
      (ArmClasses.parameter (NestedClassCell.point left width t 0) 0 (t 2)) ζ‖ := by
  have hy : 0 < NestedClassCell.point left width t 0 := by
    simp only [NestedClassCell.point,left,width,Matrix.cons_val_zero,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]
    nlinarith [(ht 0).1]
  have hs (i : Fin 3) (hi : i=1 ∨ i=2) :
      NestedClassCell.point left width t i=t i := by
    have hl : left i=0 := by rcases hi with rfl | rfl <;> decide +kernel
    have hw : width i=1 := by rcases hi with rfl | rfl <;> decide +kernel
    simp only [NestedClassCell.point,hl,hw,Rat.cast_zero,Rat.cast_one,zero_add,one_mul]
  have h := NestedClassCell.logarithm_lower 1 0 0 (1/5) (13/10) (13/100) 0 12
    poly affine degrees left width program_checked affine_checked signs_checked logarithm_checked
    (by norm_num) (by norm_num) t ht hy
    (by rw [hs 1 (Or.inl rfl)]; exact ht 1)
    (by rw [hs 2 (Or.inr rfl)]; exact ht 2) ζ (by simpa only [Rat.cast_one] using hζ)
  simpa only [hs 1 (Or.inl rfl),hs 2 (Or.inr rfl)] using h
#print axioms program_checked
#print axioms affine_checked
#print axioms signs_checked
#print axioms logarithm_checked
#print axioms actual_cell
end
end Gebendorfer.RadenkovicGutman.NestedCellControl
