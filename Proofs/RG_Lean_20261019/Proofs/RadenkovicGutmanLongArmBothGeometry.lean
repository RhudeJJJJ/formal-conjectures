/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLongArmGeometry1L
import Proofs.RadenkovicGutmanNestedHornerTransform
namespace Gebendorfer.RadenkovicGutman.LongArmBothFamily
open Focus CoreQuotient Set MeasureTheory
open scoped Classical
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
def P (y v : ℝ) : ℝ := LongArmFamily1L.Q y v
def Q (y t : ℝ) : ℝ := LongArmFamily1L.Q y t
def scaleFactor (y v t : ℝ) : ℝ := y^4/(LongArmFamily1L.qDen y v * LongArmFamily1L.qDen y t)^4
theorem scaleFactor_nonneg (y v t : ℝ) (hy : 0 < y) : 0 ≤ scaleFactor y v t := by
  unfold scaleFactor LongArmFamily1L.qDen
  positivity
#print axioms scaleFactor_nonneg
end
end Gebendorfer.RadenkovicGutman.LongArmBothFamily
