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
noncomputable def leaf01504_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 5428269874256281600000000000 5753101197998167147142299539 1778117590034121240562500000000))
theorem leaf01504_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 5428269874256281600000000000 5753101197998167147142299539 1778117590034121240562500000000 leaf01504_w_raw=true := by decide +kernel
theorem leaf01504_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01504_w_raw=true := by decide +kernel
#print axioms leaf01504_raw
#print axioms leaf01504_rectangular
noncomputable def leaf01504_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01504_w_raw ![12,30,15] ![1,1,1] ![64,32,16])
theorem leaf01504_inner : leaf01504_w_inner=IntegerAffineStages.inner leaf01504_w_raw ![12,30,15] ![1,1,1] ![64,32,16] := by decide +kernel
#print axioms leaf01504_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
