/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeInterpolation
import Proofs.RadenkovicGutmanLongArmBothCoefficientJ00
import Proofs.RadenkovicGutmanLongArmBothCoefficientJ02
import Proofs.RadenkovicGutmanLongArmBothCoefficientJ03
import Proofs.RadenkovicGutmanLongArmBothCoefficientJ04
import Proofs.RadenkovicGutmanLongArmBothCoefficientJ05
namespace Gebendorfer.RadenkovicGutman.LongArmBothFamily
open Focus CoreQuotient DegreeInterpolation
noncomputable section
set_option maxHeartbeats 0
theorem coefficient_J_all (d y v t : ℝ) (hy : 0 < y) : (Complex.normSq (b d y (P y v) (Q y t)) - Complex.normSq (a d (P y v) (Q y t)))^2 = scaleFactor y v t * jp d y v t := by
  change lhsJ d y (P y v) (Q y t) = _
  rw [lhs_J, poly_J]
  unfold blend lhsJ
  dsimp only
  rw [coefficient_J00 y v t hy, coefficient_J02 y v t hy, coefficient_J03 y v t hy,
    coefficient_J04 y v t hy, coefficient_J05 y v t hy]
  ring
#print axioms coefficient_J_all
end
end Gebendorfer.RadenkovicGutman.LongArmBothFamily
