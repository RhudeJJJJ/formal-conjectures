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
noncomputable def leaf01262_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 19127840306410553344000000000000 23484845195267050033586119277283 659161204620484580821500000000000))
theorem leaf01262_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 19127840306410553344000000000000 23484845195267050033586119277283 659161204620484580821500000000000 leaf01262_w_raw=true := by decide +kernel
theorem leaf01262_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01262_w_raw=true := by decide +kernel
#print axioms leaf01262_raw
#print axioms leaf01262_rectangular
noncomputable def leaf01262_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01262_w_raw ![8,6,3] ![1,1,1] ![16,8,4])
theorem leaf01262_inner : leaf01262_w_inner=IntegerAffineStages.inner leaf01262_w_raw ![8,6,3] ![1,1,1] ![16,8,4] := by decide +kernel
#print axioms leaf01262_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
