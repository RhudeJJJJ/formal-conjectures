/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
An exact bridge for physical arms 1 and any length at least five.
The residual degree is a real parameter; no numerical degree interpolation is trusted.
-/
import Proofs.RadenkovicGutmanConcreteGraphQuotient
import Proofs.RadenkovicGutmanMixedGraphIntegral
import Proofs.RadenkovicGutmanArmClasses
import Proofs.RadenkovicGutmanNestedHornerCells
import Proofs.RadenkovicGutmanRationalLog
namespace Gebendorfer.RadenkovicGutman.LongArmFamily1L
open Focus CoreQuotient Set MeasureTheory
open scoped Classical
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
def pNum (y t : ℝ) : ℝ := (1 : ℝ) * y ^ 1 * t ^ 0
def pDen (y t : ℝ) : ℝ := (1 : ℝ) * y ^ 0 * t ^ 0
def qNum (y t : ℝ) : ℝ := (9 : ℝ) * y ^ 2 * t ^ 0 + (24 : ℝ) * y ^ 4 * t ^ 0 + (22 : ℝ) * y ^ 6 * t ^ 0 + (8 : ℝ) * y ^ 8 * t ^ 0 + (1 : ℝ) * y ^ 10 * t ^ 0 + (1 : ℝ) * y ^ 0 * t ^ 1
def qDen (y t : ℝ) : ℝ := (3 : ℝ) * y ^ 1 * t ^ 0 + (13 : ℝ) * y ^ 3 * t ^ 0 + (16 : ℝ) * y ^ 5 * t ^ 0 + (7 : ℝ) * y ^ 7 * t ^ 0 + (1 : ℝ) * y ^ 9 * t ^ 0
def P (y t : ℝ) : ℝ := pNum y t / pDen y t
def Q (y t : ℝ) : ℝ := qNum y t / qDen y t
def scaleFactor (y t : ℝ) : ℝ := y ^ 4 / (pDen y t * qDen y t) ^ 4
theorem rho_p (y t : ℝ) (hy : 0 < y) : PathEnclosure.rho y 0 = P y t := by
  have hy0 : y ≠ 0 := hy.ne'
  simp only [PathEnclosure.rho, PathEnclosure.arm]
  unfold P pNum pDen
  field_simp
  ring

theorem parameter_q (y t : ℝ) (hy : 0 < y) :
    ArmClasses.parameter y 4 t = Q y t := by
  have hy0 : y ≠ 0 := hy.ne'
  have h5 : 0 < y^4+3*y^2+1 := by positivity
  have h6 : 0 < y^4+4*y^2+3 := by positivity
  change y+(PathEnclosure.lower y+t*(PathEnclosure.upper y-PathEnclosure.lower y))/y = Q y t
  have hqp : 0 < qDen y t := by unfold qDen; positivity
  rw [PathEnclosure.interval_width y hy]
  unfold PathEnclosure.lower Q qNum qDen
  field_simp
  ring

theorem actual_q (y : ℝ) (hy : 0 < y) (q : ℕ) (hq : 4 ≤ q) :
    ∃ t ∈ Icc (0 : ℝ) 1, PathEnclosure.rho y q = Q y t := by
  obtain ⟨t, ht, he⟩ := ArmClasses.actual_parameter y hy q
  refine ⟨t, ht, ?_⟩
  have hc : ArmClasses.classify q = (4 : Fin 5) := by
    apply Fin.ext
    change min q 4 = 4
    omega
  rw [hc, parameter_q y t hy] at he
  exact he

theorem P_ge (y t : ℝ) (hy : 0 < y) : y ≤ P y t := by
  rw [← rho_p y t hy]
  exact le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y _) hy.le)

theorem Q_ge (y t : ℝ) (hy : 0 < y) (ht : 0 ≤ t) : y ≤ Q y t := by
  rw [← parameter_q y t hy]
  change y ≤ y+(PathEnclosure.lower y+t*(PathEnclosure.upper y-PathEnclosure.lower y))/y
  exact le_add_of_nonneg_right (div_nonneg (add_nonneg (show 0 ≤ PathEnclosure.lower y by unfold PathEnclosure.lower; positivity) (mul_nonneg ht (ArmClasses.long_width_pos y hy).le)) hy.le)

theorem scaleFactor_nonneg (y t : ℝ) (hy : 0 < y) : 0 ≤ scaleFactor y t := by
  unfold scaleFactor pDen qDen
  positivity

#print axioms actual_q
#print axioms Q_ge
end
end Gebendorfer.RadenkovicGutman.LongArmFamily1L
