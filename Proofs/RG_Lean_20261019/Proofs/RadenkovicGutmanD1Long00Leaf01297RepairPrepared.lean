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
noncomputable def leaf01297_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 3461470391132749824000000000000 4154231976601143180326390736357 161079401087088870529000000000000))
theorem leaf01297_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 3461470391132749824000000000000 4154231976601143180326390736357 161079401087088870529000000000000 leaf01297_w_raw=true := by decide +kernel
theorem leaf01297_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01297_w_raw=true := by decide +kernel
#print axioms leaf01297_raw
#print axioms leaf01297_rectangular
noncomputable def leaf01297_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01297_w_raw ![14,7,6] ![1,1,1] ![32,8,8])
theorem leaf01297_inner : leaf01297_w_inner=IntegerAffineStages.inner leaf01297_w_raw ![14,7,6] ![1,1,1] ![32,8,8] := by decide +kernel
#print axioms leaf01297_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
