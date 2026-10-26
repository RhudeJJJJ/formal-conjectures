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
noncomputable def leaf01434_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 388597533297659084800000000000 425935886483579903901374616417 62768650369120063406200000000000))
theorem leaf01434_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 388597533297659084800000000000 425935886483579903901374616417 62768650369120063406200000000000 leaf01434_w_raw=true := by decide +kernel
theorem leaf01434_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01434_w_raw=true := by decide +kernel
#print axioms leaf01434_raw
#print axioms leaf01434_rectangular
noncomputable def leaf01434_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01434_w_raw ![16,14,7] ![1,1,1] ![64,16,8])
theorem leaf01434_inner : leaf01434_w_inner=IntegerAffineStages.inner leaf01434_w_raw ![16,14,7] ![1,1,1] ![64,16,8] := by decide +kernel
#print axioms leaf01434_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
