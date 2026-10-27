/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01404_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 9753454291334463488000000000000 10873289392723130214743034494193 1197022637999670489976500000000000))
theorem leaf01404_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 9753454291334463488000000000000 10873289392723130214743034494193 1197022637999670489976500000000000 leaf01404_w_raw=true := by decide +kernel
theorem leaf01404_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01404_w_raw=true := by decide +kernel
#print axioms leaf01404_raw
#print axioms leaf01404_rectangular
noncomputable def leaf01404_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01404_w_raw ![18,62,31] ![1,1,1] ![64,64,32])
theorem leaf01404_inner : leaf01404_w_inner=IntegerAffineStages.inner leaf01404_w_raw ![18,62,31] ![1,1,1] ![64,64,32] := by decide +kernel
#print axioms leaf01404_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
