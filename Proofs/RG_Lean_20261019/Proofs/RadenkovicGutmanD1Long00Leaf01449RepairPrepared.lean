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
noncomputable def leaf01449_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 6190248001215135744000000000000 6727425858348204230525876735439 1166919081521386760481500000000000))
theorem leaf01449_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 6190248001215135744000000000000 6727425858348204230525876735439 1166919081521386760481500000000000 leaf01449_w_raw=true := by decide +kernel
theorem leaf01449_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01449_w_raw=true := by decide +kernel
#print axioms leaf01449_raw
#print axioms leaf01449_rectangular
noncomputable def leaf01449_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01449_w_raw ![15,6,3] ![1,1,1] ![64,8,4])
theorem leaf01449_inner : leaf01449_w_inner=IntegerAffineStages.inner leaf01449_w_raw ![15,6,3] ![1,1,1] ![64,8,4] := by decide +kernel
#print axioms leaf01449_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
