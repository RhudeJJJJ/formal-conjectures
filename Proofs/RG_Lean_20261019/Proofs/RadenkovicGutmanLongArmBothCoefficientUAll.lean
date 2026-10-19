/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeInterpolation
import Proofs.RadenkovicGutmanLongArmBothCoefficientU00
import Proofs.RadenkovicGutmanLongArmBothCoefficientU02
import Proofs.RadenkovicGutmanLongArmBothCoefficientU03
import Proofs.RadenkovicGutmanLongArmBothCoefficientU04
import Proofs.RadenkovicGutmanLongArmBothCoefficientU05
namespace Gebendorfer.RadenkovicGutman.LongArmBothFamily
open Focus CoreQuotient DegreeInterpolation
noncomputable section
set_option maxHeartbeats 0
theorem coefficient_U_all (d y v t : ℝ) (hy : 0 < y) : Complex.normSq (b d y (P y v) (Q y t) * star (e d y (P y v) (Q y t)) - a d (P y v) (Q y t) * star (c d y (P y v) (Q y t))) = scaleFactor y v t * up d y v t := by
  change lhsU d y (P y v) (Q y t) = _
  rw [lhs_U, poly_U]
  unfold blend lhsU
  dsimp only
  rw [coefficient_U00 y v t hy, coefficient_U02 y v t hy, coefficient_U03 y v t hy,
    coefficient_U04 y v t hy, coefficient_U05 y v t hy]
  ring
#print axioms coefficient_U_all
end
end Gebendorfer.RadenkovicGutman.LongArmBothFamily
