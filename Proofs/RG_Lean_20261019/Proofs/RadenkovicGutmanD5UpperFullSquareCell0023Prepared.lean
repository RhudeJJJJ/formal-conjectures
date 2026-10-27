/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD5Long00CompositionalIntegerNorm
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial FixedDegree05Long00CompositionalIntegerNorm.pack false 3397310043048494197631902285824000000000000 588654193664713519532850443010176351361 25570237913770127523694867923250000000000))
theorem leaf00023_raw : IntegerNormProgramPack.rawCheck FixedDegree05Long00CompositionalIntegerNorm.pack false 3397310043048494197631902285824000000000000 588654193664713519532850443010176351361 25570237913770127523694867923250000000000 leaf00023_w_raw=true := by decide +kernel
theorem leaf00023_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf00023_w_raw=true := by decide +kernel
#print axioms leaf00023_raw
#print axioms leaf00023_rectangular
noncomputable def leaf00023_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf00023_w_raw ![27,0,0] ![1,1,1] ![3200,1,1])
theorem leaf00023_inner : leaf00023_w_inner=IntegerAffineStages.inner leaf00023_w_raw ![27,0,0] ![1,1,1] ![3200,1,1] := by decide +kernel
#print axioms leaf00023_inner
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
