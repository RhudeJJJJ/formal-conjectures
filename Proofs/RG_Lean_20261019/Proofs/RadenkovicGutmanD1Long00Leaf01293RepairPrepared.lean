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
noncomputable def leaf01293_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 6923330734425899008000000000000 8308973498790604464787952412367 322160413187991945731500000000000))
theorem leaf01293_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 6923330734425899008000000000000 8308973498790604464787952412367 322160413187991945731500000000000 leaf01293_w_raw=true := by decide +kernel
theorem leaf01293_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01293_w_raw=true := by decide +kernel
#print axioms leaf01293_raw
#print axioms leaf01293_rectangular
noncomputable def leaf01293_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01293_w_raw ![14,1,0] ![1,1,1] ![32,2,2])
theorem leaf01293_inner : leaf01293_w_inner=IntegerAffineStages.inner leaf01293_w_raw ![14,1,0] ![1,1,1] ![32,2,2] := by decide +kernel
#print axioms leaf01293_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
